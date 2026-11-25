#!/usr/bin/env python3
"""DAG scheduler for proof-approach.

One node is one held-out problem.  Ready nodes get their own run (created by
new_run.py) and one or more OMP CLI workers.  The scheduler starts a node's
workers together, polls the run's events.jsonl, kills the remaining workers at
the first green check, and releases dependent nodes.

This is deliberately smaller than a full controller.  It is the H5 prototype:
per-node method choice, first-green kill, dependency gating, and a dry-run
command plan.

Usage:
  python3 harness/dag.py --dag experiments/h5-demo.json --dry-run
  PA_LOCAL=1 python3 harness/dag.py --dag experiments/h5-demo.json --spawn

DAG JSON:
  {
    "id": "h5-demo",
    "nodes": [
      {"id": "gcd", "problem": "easy/gcd", "deps": [], "method": "S0",
       "agents": 1, "budget_s": 1800},
      {"id": "stack", "problem": "easy/stack", "deps": [], "method": "S0",
       "agents": 1, "budget_s": 1800}
    ]
  }

`method` is the method used inside the node; `agents` is the lane count for
that node.  The scheduler itself is the DAG method.
"""
from __future__ import annotations

import argparse
import json
import os
import shlex
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HARNESS = Path(__file__).resolve().parent
NEW_RUN = HARNESS / "new_run.py"
PA = HARNESS / "pa.py"


@dataclass
class Node:
    id: str
    problem: str
    deps: list[str] = field(default_factory=list)
    method: str = "S0"
    agents: int = 1
    budget_s: int = 1800

    @property
    def run_id(self) -> str:
        return f"{self.id}"


@dataclass
class NodeState:
    node: Node
    run_id: str | None = None
    processes: list[subprocess.Popen] = field(default_factory=list)
    started: float | None = None
    status: str = "pending"  # pending | running | solved | failed | blocked
    reason: str = ""


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def load_dag(path: Path) -> tuple[str, list[Node]]:
    raw = json.loads(path.read_text())
    dag_id = raw.get("id")
    if not dag_id:
        raise SystemExit("DAG needs an id")
    nodes = []
    for item in raw.get("nodes", []):
        node = Node(
            id=item["id"],
            problem=item["problem"],
            deps=list(item.get("deps", [])),
            method=item.get("method", "S0"),
            agents=int(item.get("agents", 1)),
            budget_s=int(item.get("budget_s", 1800)),
        )
        if node.agents < 1:
            raise SystemExit(f"node {node.id}: agents must be >= 1")
        nodes.append(node)
    return dag_id, nodes


def validate(nodes: list[Node]) -> None:
    ids = {n.id for n in nodes}
    if len(ids) != len(nodes):
        raise SystemExit("duplicate node id")
    for n in nodes:
        for dep in n.deps:
            if dep not in ids:
                raise SystemExit(f"node {n.id}: unknown dependency {dep}")
            if dep == n.id:
                raise SystemExit(f"node {n.id}: self dependency")
    # Cycle check.
    state: dict[str, int] = {}

    def visit(n: str) -> None:
        if state.get(n) == 1:
            raise SystemExit(f"dependency cycle at {n}")
        if state.get(n) == 2:
            return
        state[n] = 1
        for dep in next(x for x in nodes if x.id == n).deps:
            visit(dep)
        state[n] = 2

    for n in nodes:
        visit(n.id)


def run(cmd: list[str], cwd: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, env=env)


def ensure_run(dag_id: str, node: Node, dry: bool, env: dict[str, str]) -> str:
    run_id = f"{dag_id}-{node.id}"
    run_dir = ROOT / "runs" / run_id
    if run_dir.exists():
        return run_id
    if dry:
        print(
            f"DRY create {run_id}: {sys.executable} {NEW_RUN} --method {node.method} "
            f"--problems {node.problem} --agents {node.agents} --budget-s {node.budget_s} "
            f"--run-id {run_id}"
        )
        return run_id
    proc = run(
        [
            sys.executable,
            str(NEW_RUN),
            "--method",
            node.method,
            "--problems",
            node.problem,
            "--agents",
            str(node.agents),
            "--budget-s",
            str(node.budget_s),
            "--run-id",
            run_id,
        ],
        ROOT,
        env,
    )
    if proc.returncode != 0:
        raise SystemExit(f"new_run failed for {run_id}:\n{proc.stdout}\n{proc.stderr}")
    print(f"created {run_id}")
    return run_id


def start_run(run_id: str, dry: bool, env: dict[str, str]) -> None:
    if dry:
        print(f"DRY start {run_id}: {sys.executable} {PA} start --run {run_id}")
        return
    proc = run([sys.executable, str(PA), "start", "--run", run_id], ROOT, env)
    if proc.returncode != 0:
        raise SystemExit(f"pa.py start failed for {run_id}:\n{proc.stdout}\n{proc.stderr}")


def worker_prompt(run_id: str, agent: str) -> str:
    return (
        f"You are {agent} in DAG run {run_id}. Read BRIEF.md first. "
        "Work only in this workspace. Do not spawn subagents, do not read other "
        "workspaces or runs, and do not use a reference proof. Run the pa.py check "
        "from the brief after a coherent change. If every target is green, stop. "
        "If the statement is false, report the precise counterexample or failed "
        "premise; do not weaken it and do not add axioms."
    )


def spawn_node(dag_id: str, node: Node, run_id: str, dry: bool, env: dict[str, str]) -> NodeState:
    state = NodeState(node=node, run_id=run_id, started=time.monotonic(), status="running")
    run_dir = ROOT / "runs" / run_id
    for i in range(node.agents):
        agent = f"a{i + 1}"
        ws = run_dir / "agents" / agent / "workspace"
        log = run_dir / "logs" / f"dag-{agent}.log"
        log.parent.mkdir(parents=True, exist_ok=True)
        cmd = [
            "omp",
            "-p",
            "--cwd",
            str(ws),
            "--no-session",
            "--no-title",
            "--auto-approve",
            "--max-time",
            str(node.budget_s),
            "--tools",
            "bash,read,write,edit,glob,grep",
            worker_prompt(run_id, agent),
        ]
        if dry:
            print(f"DRY spawn {node.id}/{agent}: " + " ".join(shlex.quote(x) for x in cmd))
            continue
        handle = open(log, "ab")
        p = subprocess.Popen(
            cmd,
            cwd=ROOT,
            stdout=handle,
            stderr=subprocess.STDOUT,
            env=env,
            start_new_session=True,
        )
        state.processes.append(p)
    return state


def node_solved(run_id: str) -> bool:
    path = ROOT / "runs" / run_id / "events.jsonl"
    if not path.is_file():
        return False
    for line in path.read_text(errors="replace").splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("kind") == "check" and event.get("solved") is True:
            return True
    return False


def stop_node(state: NodeState) -> None:
    for p in state.processes:
        if p.poll() is not None:
            continue
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGTERM)
        except ProcessLookupError:
            pass
    deadline = time.monotonic() + 10
    for p in state.processes:
        try:
            p.wait(timeout=max(0.1, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dag", required=True, type=Path)
    ap.add_argument("--dry-run", action="store_true", help="print the schedule, do not create or spawn")
    ap.add_argument("--spawn", action="store_true", help="create runs and spawn OMP workers")
    ap.add_argument("--timeout-s", type=int, default=None)
    args = ap.parse_args()

    if args.spawn == args.dry_run:
        sys.exit("choose exactly one of --dry-run or --spawn")

    dag_id, nodes = load_dag(args.dag)
    validate(nodes)
    env = os.environ.copy()
    env.setdefault("PA_LOCAL", "1")

    states: dict[str, NodeState] = {n.id: NodeState(node=n) for n in nodes}
    started = time.monotonic()
    hard_deadline = started + args.timeout_s if args.timeout_s else None

    print(f"DAG {dag_id}: {len(nodes)} nodes")
    if args.dry_run:
        for s in states.values():
            if any(states[d].status == "failed" for d in s.node.deps):
                s.status = "blocked"
                continue
            s.run_id = ensure_run(dag_id, s.node, True, env)
            start_run(s.run_id, True, env)
            spawn_node(dag_id, s.node, s.run_id, True, env)
            s.status = "scheduled"
        print("\nDAG dry-run complete")
        return 0

    while True:
        # Mark dependency-blocked nodes.
        for s in states.values():
            if s.status == "pending" and any(states[d].status in {"failed", "blocked"} for d in s.node.deps):
                s.status = "blocked"
                s.reason = "dependency failed"

        ready = [
            s for s in states.values()
            if s.status == "pending" and all(states[d].status == "solved" for d in s.node.deps)
        ]
        for s in ready:
            s.run_id = ensure_run(dag_id, s.node, args.dry_run, env)
            start_run(s.run_id, args.dry_run, env)
            states[s.node.id] = spawn_node(dag_id, s.node, s.run_id, args.dry_run, env)
            print(f"{now()} start {s.node.id} ({s.node.method}, {s.node.agents} lane(s)) -> {s.run_id}")

        if args.dry_run:
            # Print all nodes in dependency order by repeatedly releasing.
            for s in states.values():
                if s.status == "pending":
                    s.status = "solved"
            if all(s.status == "solved" for s in states.values()):
                break
            continue

        # Poll running nodes.
        running = [s for s in states.values() if s.status == "running"]
        for s in running:
            if node_solved(s.run_id or ""):
                s.status = "solved"
                stop_node(s)
                elapsed = time.monotonic() - (s.started or time.monotonic())
                print(f"{now()} solved {s.node.id} in {elapsed:.1f}s; stopped siblings")
            elif s.started is not None and time.monotonic() - s.started > s.node.budget_s:
                s.status = "failed"
                s.reason = "node budget expired"
                stop_node(s)
                print(f"{now()} failed {s.node.id}: budget")

        if hard_deadline and time.monotonic() > hard_deadline:
            for s in states.values():
                if s.status == "running":
                    s.status = "failed"
                    s.reason = "DAG deadline"
                    stop_node(s)
            break

        if all(s.status in {"solved", "failed", "blocked"} for s in states.values()):
            break
        if not any(s.status == "running" for s in states.values()):
            # No ready node, no running node: deadlock or all pending blocked.
            for s in states.values():
                if s.status == "pending":
                    s.status = "blocked"
                    s.reason = "no ready dependency state"
            break
        time.sleep(2)

    print("\nDAG result:")
    for s in states.values():
        print(f"  {s.node.id:20s} {s.status:8s} {s.reason}")
    return 0 if all(s.status == "solved" for s in states.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
