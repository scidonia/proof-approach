#!/usr/bin/env python3
"""Create a run directory: copied statements, per-agent workspaces, hashes.

A run is the unit the scorer reads.  It records which method, which problems,
which agents, the wall-clock budget, and the digest of every statement the
agents were given.  Statements are copied into each workspace; reference
answers are never copied because none are stored in the repository.

Usage:
  new_run.py --method S1 --problems easy/gcd,easy/sort --agents 4 --budget-s 1800
  new_run.py --method S0 --tier smoke --agents 1 --budget-s 300 --run-id pilot-smoke
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
METHODS = {
    "S0": ("S0_serial", 1),
    "S1": ("S1_blind_race", 4),
    # Four workers plus the supervisor the method is named for.
    "S2": ("S2_crosstalk", 5),
    "S3": ("S3_lemma_cutting", 5),
    "S4": ("S4_large_swarm", 8),
    "S5": ("S5_warm_portfolio", 3),
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def select_problems(manifest: dict, ids: str | None, tier: str | None) -> list[dict]:
    problems = manifest["problems"]
    if tier:
        problems = [p for p in problems if p["tier"] == tier]
    if ids:
        wanted = [x.strip() for x in ids.split(",") if x.strip()]
        by_id = {p["id"]: p for p in problems}
        missing = [w for w in wanted if w not in by_id]
        if missing:
            sys.exit(f"unknown problem(s) for this selection: {missing}")
        problems = [by_id[w] for w in wanted]
    if not problems:
        sys.exit("no problems selected")
    return problems


def proof_skeleton(problem: dict) -> str:
    lines = [
        f"import Problems.{problem['path'].replace('/', '.')}",
        "",
        f"/- Targets for `{problem['id']}`.  Required declarations:",
    ]
    for t in problem["targets"]:
        lines.append(f"     theorem {t['proof']} : {problem['namespace']}.{t['name']}")
    lines += [
        "",
        "Add helper lemmas here or in other `Proofs.*` modules.  Keep this module",
        "compiling; the harness builds it and then checks each target by type and",
        "by axiom footprint.",
        "-/",
        "",
        f"namespace {problem['namespace']}",
        "",
        "-- proofs here",
        "",
        f"end {problem['namespace']}",
        "",
    ]
    return "\n".join(lines)


def supervisor_brief(problems: list[dict], run: dict, targets: str) -> str:
    board = f"runs/{run['run_id']}/shared/board.md"
    broadcast = f"runs/{run['run_id']}/shared/broadcast.md"
    if run["method"] == "S2":
        duty = f"""Your tool is the board: read `{board}`, verify each claimed
checkpoint by running the worker's check (or reading the event it produced),
and write `{broadcast}` with only what you verified.  Broadcast a usable
declaration with its fully-qualified name and workspace path, an approach that
failed and why, and at most one next suggestion per worker.  You do not prove
the target yourself; you keep the swarm from repeating a dead end and make a
green lemma reachable by the others."""
    else:
        duty = f"""Your tool is the cut.  Before workers start a problem, write
`runs/{run['run_id']}/shared/plan.md` with exact Lean lemma statements, an
owner per lemma, its dependencies, and the integration file.  A lemma statement
must elaborate.  Copy a verified lemma into `shared/workspace/Proofs/` under a
unique name and tell its dependents.  Re-cut a lemma that has not moved in a
third of the remaining budget.  You own the assembled root module; a problem is
green only when the root checks in `shared/workspace`."""
    return f"""# Run brief: {run['run_id']}

You are **a1** (supervisor) in method **{run['method']}**.

Your workspace is `runs/{run['run_id']}/shared/workspace`.  The workers' private
workspaces are under `runs/{run['run_id']}/agents/`; you may read them but you
may not edit them.  The run budget is {run['budget_s']} seconds; the clock
started when this brief was handed out.  You are one supervisor: do not spawn
subagents; all orchestration belongs to the conductor.

## Targets

{targets}

## Duty

{duty}

## Checking your own work

Use `--agent shared` for a check you run in the shared workspace:

```bash
nix develop {ROOT} -c python3 {ROOT}/harness/pa.py check --run {run['run_id']} --agent shared --problem <id>
```

The statement modules are read-only and hashed.  A target is accepted only on
the exact declared type and an allowed axiom footprint.  Do not run `lake`,
`lean`, or `nix develop … lake` directly; compile through `pa.py check` on the
worker.

## Honesty

The rules in the worker brief apply to you unchanged: no reference proof, no
other run, no `../lean-llvm`, no web search for the theorem.  Report an
exposure with `pa.py note --cheat`.

## Reporting

Append a note when a problem is green, with the wall-clock time and which
worker's declarations it used.  For S3 also record re-cuts and unused lemmas;
for S2 record checkpoints broadcast and imports by another worker.
"""


def brief(problems: list[dict], run: dict, agent: str, ws_rel: str) -> str:
    blocks = []
    for problem in problems:
        targets = "\n".join(
            f"- `{problem['namespace']}.{t['proof']}` : `{problem['namespace']}.{t['name']}` — {t['desc']}"
            for t in problem["targets"]
        )
        blocks.append(f"### `{problem['id']}` (`{problem['tier']}`)\n\n{targets}")
    targets = "\n\n".join(blocks)
    supervisor_method = run["method"] in {"S2", "S3"}
    if supervisor_method and agent in {"a1", "shared"}:
        return supervisor_brief(problems, run, targets)

    coordination = ""
    if run["method"] == "S2":
        coordination = f"""
## Coordination: cross-talk

The board is `runs/{run['run_id']}/shared/board.md`; the broadcast is
`runs/{run['run_id']}/shared/broadcast.md`.  After a kernel-checked checkpoint,
append to the board in the format the method brief names, then end your turn.
The conductor wakes the supervisor, then wakes you with the new broadcast.
Read the broadcast before starting a new attempt and after every checkpoint.
Copy a broadcast declaration into your own workspace with a comment naming the
source agent; never edit another workspace.
"""
    elif run["method"] == "S3":
        coordination = f"""
## Coordination: lemma cutting

The supervisor's plan is `runs/{run['run_id']}/shared/plan.md`.  Prove only the
lemmas assigned to you, in your own workspace, and report a checkpoint when one
builds.  The supervisor copies a verified lemma into `shared/workspace`; it
owns the assembled root.  If your assignment is blocked on a missing
dependency, say so and end your turn rather than guessing at the statement.
"""
    return f"""# Run brief: {run['run_id']}

You are **{agent}** (worker) in method **{run['method']}**.

Workspace: `{ws_rel}` (all paths below are relative to it unless absolute).

Budget: {run['budget_s']} seconds of wall clock for the whole run.  The clock
started when this brief was handed out.

You are one worker.  Do not spawn subagents or delegate the proof; all
orchestration belongs to the conductor.
{coordination}
## Your problems

{targets}

The statement modules under `Problems/` are read-only.  Their digest is
recorded; editing one fails every target in that problem.  Work only under
`Proofs/`.

## Checking

Run a check after every meaningful change:

```bash
nix develop {ROOT} -c python3 {ROOT}/harness/pa.py check --run {run['run_id']} --agent {agent} --problem <id>
```

The command builds `Proofs.<path>`, type-checks each declared target against
the statement, prints the axiom footprint, and appends an event.  A target is
accepted only when:

* the proof declaration has exactly the target's type, and
* the axiom footprint is a subset of `propext`, `Classical.choice`,
  `Quot.sound` (no `sorryAx`, no `ofReduceBool` from `native_decide`).

The harness rejects `axiom`, `unsafe`, `opaque`, `native_decide`,
`implemented_by` and `@[extern]` anywhere under `Proofs/`.

Do not run `lake`, `lean`, or `nix develop … lake` directly in a workspace.
Compilation is on the worker through `pa.py check`; a direct local elaboration
can exhaust this host's memory and is not part of the measured method.

## Honesty

Do not look for an answer.  Specifically, do not:

* read another agent's workspace, another run's directory, or `solutions/`;
* read `../lean-llvm` or any other checkout, or a Git history;
* search the web or query any network service for the theorem;
* ask a model or tool for the proof text.

Use Lean, the library sources it ships with, and your own reasoning.  If you
are exposed to a proof of a target by accident, stop and report it with:

```bash
nix develop {ROOT} -c python3 {ROOT}/harness/pa.py note --run {run['run_id']} --agent {agent} --cheat --text "<what you saw and where>"
```

A confirmed exposure invalidates the run and it is repeated.

## Reporting

When you believe every target of a problem is proved, run the check.  When it
is green, append a one-paragraph note with the approach and the wall-clock
time at which it went green:

```bash
nix develop {ROOT} -c python3 {ROOT}/harness/pa.py note --run {run['run_id']} --agent {agent} --text "<summary>"
```

Do not keep polishing a green proof.
"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--method", required=True, choices=sorted(METHODS))
    ap.add_argument("--problems", default=None, help="comma-separated ids; default: the tier")
    ap.add_argument("--tier", default=None, choices=["smoke", "easy", "medium", "hard"])
    ap.add_argument("--agents", type=int, default=None)
    ap.add_argument("--budget-s", type=int, default=None)
    ap.add_argument("--run-id", default=None)
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()

    manifest = json.loads((ROOT / "problems" / "manifest.json").read_text())
    problems = select_problems(manifest, args.problems, args.tier)
    prompt_name, default_agents = METHODS[args.method]
    agents_n = args.agents or default_agents
    run_id = args.run_id or f"{args.method.lower()}-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
    run_dir = ROOT / "runs" / run_id
    if run_dir.exists() and not args.force:
        sys.exit(f"run directory exists: {run_dir} (use --force)")
    if run_dir.exists():
        shutil.rmtree(run_dir)
    budget = args.budget_s or max(p["budget_s"] for p in problems)

    # Copy the statement tree once; every workspace gets its own copy so a
    # blind agent cannot read another's proof files by accident.
    statement_files = {
        p["id"]: {
            "path": p["path"],
            "sha256": sha256_file(ROOT / "Problems" / (p["path"] + ".lean")),
        }
        for p in problems
    }
    run_manifest = {"version": 1, "problems": []}
    for p in problems:
        q = dict(p)
        q["statement_sha256"] = statement_files[p["id"]]["sha256"]
        run_manifest["problems"].append(q)

    remote_cfg = None
    if not os.environ.get("PA_LOCAL") and (ROOT / ".remote.json").is_file():
        try:
            remote_cfg = json.loads((ROOT / ".remote.json").read_text())
        except json.JSONDecodeError:
            remote_cfg = None

    agent_names = [f"a{i + 1}" for i in range(agents_n)]
    run = {
        "run_id": run_id,
        "method": args.method,
        "method_name": prompt_name,
        "created": utc_now(),
        "started_at": None,
        "ended_at": None,
        "end_reason": None,
        "budget_s": budget,
        "problems": [p["id"] for p in problems],
        "agents": agent_names,
        "workspaces": {},
        "shared": "shared/workspace",
        "prompt": f"methods/{prompt_name}.md",
        "prompt_sha256": sha256_file(ROOT / "methods" / f"{prompt_name}.md"),
        "manifest_sha256": None,
        "model": "session default",
        "notes": "",
    }

    def make_workspace(ws: Path, agent: str) -> None:
        ws.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / "lakefile.toml", ws / "lakefile.toml")
        shutil.copy2(ROOT / "lean-toolchain", ws / "lean-toolchain")
        shutil.copytree(ROOT / "Problems", ws / "Problems")
        shutil.copy2(ROOT / "Problems.lean", ws / "Problems.lean")
        for p in problems:
            target = ws / "Proofs" / (p["path"] + ".lean")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(proof_skeleton(p))
        (ws / "Check").mkdir(exist_ok=True)
        (ws / "REPORT.md").write_text(f"# {agent} report\n\n")
        (ws / "BRIEF.md").write_text(brief(problems, run, agent, str(ws.relative_to(run_dir))))

    for agent in agent_names:
        rel = f"agents/{agent}/workspace"
        make_workspace(run_dir / rel, agent)
        run["workspaces"][agent] = rel

    # The shared workspace exists for methods that hand lemmas through a
    # supervisor.  Race methods leave it empty and never point an agent at it.
    make_workspace(run_dir / "shared" / "workspace", "shared")
    run["workspaces"]["shared"] = "shared/workspace"
    (run_dir / "shared" / "board.md").write_text(
        "# Board\n\nCheckpoints, blockers and abandoned attempts.  Only a green "
        "`pa.py check` is a checkpoint.\n"
    )
    (run_dir / "shared" / "broadcast.md").write_text(
        "# Broadcast\n\nOnly declarations the supervisor has verified.\n"
    )
    (run_dir / "shared" / "plan.md").write_text(
        "# Plan\n\nExact lemma statements, owners and dependencies.\n"
    )

    run_manifest_path = run_dir / "manifest.json"
    run_manifest_path.write_text(json.dumps(run_manifest, indent=2) + "\n")
    run["manifest_sha256"] = sha256_file(run_manifest_path)
    (run_dir / "run.json").write_text(json.dumps(run, indent=2, sort_keys=True) + "\n")
    (run_dir / "events.jsonl").touch()
    (run_dir / "logs").mkdir(exist_ok=True)

    # Compilation belongs on the worker: the local host does not have the
    # memory for a swarm of elaborations.  The first check in each workspace
    # builds the statements there; no local `lake build` runs here.
    run["compile_backend"] = "remote" if remote_cfg else "local"
    run["worker"] = remote_cfg.get("worker") if remote_cfg else None
    (run_dir / "run.json").write_text(json.dumps(run, indent=2, sort_keys=True) + "\n")

    # Capture the dev-shell environment once, for the local fallback only, so
    # agents do not race to create the cache on their first check.
    subprocess.run(
        [sys.executable, str(ROOT / "harness" / "pa.py"), "warm"],
        cwd=ROOT, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT,
    )

    print(f"created {run_dir}")
    print(f"  method   {args.method} ({prompt_name}), {agents_n} agents")
    print(f"  problems {', '.join(p['id'] for p in problems)}")
    print(f"  budget   {budget}s")
    print(f"  start    nix develop {ROOT} -c python3 {ROOT}/harness/pa.py start --run {run_id}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
