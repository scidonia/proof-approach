#!/usr/bin/env python3
"""Proof-approach harness.

One command compiles a proof module, checks every declared target against the
statement it was declared for, rejects forbidden escape hatches, and appends a
JSON event that the scorer reads.  Every toolchain command goes through the
flake's dev shell, so nothing depends on an activated environment.

Usage:
  pa.py list
  pa.py start   --run RUN
  pa.py check   --run RUN --agent A --problem ID [--timeout S]
  pa.py note    --run RUN --agent A --text TEXT [--cheat]
  pa.py status  --run RUN
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Constructs that make a proof not a proof of the stated target, or that make
# the declaration an assertion rather than a derivation. `sorry` and `admit`
# are caught per target by the axiom check; they are also reported here so an
# agent sees them before the check.
FORBIDDEN_FATAL = [
    (r"\baxiom\b", "axiom declaration"),
    (r"\bunsafe\b", "unsafe declaration"),
    (r"\bopaque\b", "opaque declaration"),
    (r"native_decide", "native_decide (Lean.ofReduceBool)"),
    (r"implemented_by", "implemented_by attribute"),
    (r"@\[\s*extern", "extern attribute"),
]
FORBIDDEN_REPORT = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def strip_lean(src: str) -> str:
    """Remove line comments, nested block comments and string literals.

    The result is only used for pattern scans, so it needs to preserve line
    structure, not Lean's exact lexical rules.
    """
    out = []
    i = 0
    n = len(src)
    depth = 0
    in_string = False
    while i < n:
        c = src[i]
        if depth:
            if c == "/" and i + 1 < n and src[i + 1] == "-":
                depth += 1
                i += 2
                continue
            if c == "-" and i + 1 < n and src[i + 1] == "/":
                depth -= 1
                i += 2
                continue
            if c == "\n":
                out.append("\n")
            i += 1
            continue
        if in_string:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_string = False
            if c == "\n":
                out.append("\n")
            i += 1
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "-":
            depth = 1
            i += 2
            continue
        if c == "-" and i + 1 < n and src[i + 1] == "-":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if c == '"':
            in_string = True
            out.append('""')
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def scan_forbidden(proof_root: Path) -> tuple[list[str], list[str]]:
    fatal: list[str] = []
    reports: list[str] = []
    if not proof_root.is_dir():
        return fatal, reports
    for path in sorted(proof_root.rglob("*.lean")):
        rel = path.relative_to(proof_root)
        text = strip_lean(path.read_text(errors="replace"))
        for pat, why in FORBIDDEN_FATAL:
            if re.search(pat, text):
                fatal.append(f"{rel}: {why}")
        for pat, why in FORBIDDEN_REPORT:
            if re.search(pat, text):
                reports.append(f"{rel}: {why}")
    return fatal, reports


DECL_RE = re.compile(
    r"^\s*(?:theorem|lemma|def|abbrev|instance|structure|inductive)\b", re.M
)


def proof_stats(proof_root: Path) -> tuple[int, int]:
    """Lines and top-level declarations in the proof tree.

    This is the progress signal for a hard problem whose targets are still red:
    a worker that has built a de Bruijn library has done real work even when
    `solved` is false.  Comments and strings are stripped first.
    """
    if not proof_root.is_dir():
        return 0, 0
    lines = 0
    declarations = 0
    for path in sorted(proof_root.rglob("*.lean")):
        text = strip_lean(path.read_text(errors="replace"))
        lines += text.count("\n") + (1 if text and not text.endswith("\n") else 0)
        declarations += len(DECL_RE.findall(text))
    return lines, declarations


def append_event(run_dir: Path, event: dict) -> None:
    run_dir.mkdir(parents=True, exist_ok=True)
    path = run_dir / "events.jsonl"
    line = json.dumps(event, sort_keys=True) + "\n"
    with path.open("a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.write(line)
        f.flush()
        os.fsync(f.fileno())
        fcntl.flock(f, fcntl.LOCK_UN)


def load_json(path: Path) -> dict:
    with path.open() as f:
        return json.load(f)


def find_run(run: str) -> Path:
    p = Path(run)
    if not p.is_absolute():
        by_id = ROOT / "runs" / p
        p = (by_id if by_id.is_dir() else (ROOT / p)).resolve()
    if not (p / "run.json").is_file():
        sys.exit(f"not a run directory (no run.json): {p}")
    return p


def problem_map(run_dir: Path) -> dict:
    manifest = load_json(run_dir / "manifest.json")
    return {p["id"]: p for p in manifest["problems"]}


def workspace_for(run_dir: Path, run: dict, agent: str) -> Path:
    ws = run["workspaces"].get(agent)
    if ws is None:
        sys.exit(f"agent {agent!r} is not in run {run['run_id']}; known: {sorted(run['workspaces'])}")
    return run_dir / ws


def toolchain_env() -> dict[str, str]:
    """The environment `nix develop` computes for this checkout.

    The environment is captured once and cached beside the flake, keyed by the
    flake lock's digest.  It is still the dev shell's environment — nothing is
    inherited from an activated terminal — but a check does not pay a Nix
    evaluation every time.  A lock change invalidates the cache.
    """
    cache = ROOT / ".shellenv.json"
    lock = sha256_file(ROOT / "flake.lock")
    if cache.is_file():
        try:
            data = load_json(cache)
            if data.get("flake_lock") == lock:
                return data["env"]
        except (json.JSONDecodeError, KeyError):
            pass
    probe = (
        "import json, os; "
        "print('__ENV__' + json.dumps(dict(os.environ)))"
    )
    out = subprocess.check_output(
        ["nix", "develop", str(ROOT), "-c", "python3", "-c", probe],
        cwd=ROOT, text=True,
    )
    line = [l for l in out.splitlines() if l.startswith("__ENV__")][-1]
    env = json.loads(line[len("__ENV__"):])
    cache.write_text(json.dumps({"flake_lock": lock, "env": env}))
    return env


def run_command(
    cmd: list[str], cwd: Path, timeout: int, env: dict[str, str] | None = None
) -> tuple[int, str, float, bool]:
    """Run a command in its own process group, with a wall-clock timeout.

    Returns (exit code, combined output, seconds, timed_out).
    """
    started = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        start_new_session=True,
        env=env,
    )
    try:
        out, _ = proc.communicate(timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, _ = proc.communicate()
        timed_out = True
    return proc.returncode, out or "", time.monotonic() - started, timed_out


def run_lake(ws: Path, lake_args: list[str], timeout: int) -> tuple[int, str, float, bool]:
    """Run `lake` from the dev shell's cached environment, with a memory ceiling.

    Elaboration is the only thing that can grow without bound here; a cgroup
    cap makes a runaway tactic die inside its own process instead of taking
    the host with it.
    """
    env = dict(toolchain_env())
    # Lake resolves the workspace from PWD; the cached environment was captured
    # at the repository root, so it must be pointed at the workspace.
    env["PWD"] = str(ws)
    cmd = ["lake", *lake_args]
    if shutil.which("systemd-run") and not os.environ.get("PA_NO_SYSTEMD"):
        cmd = [
            "systemd-run", "--user", "--scope", "--quiet",
            "-p", "MemoryMax=3G", "-p", "MemorySwapMax=1G",
            "--", *cmd,
        ]
    code, out, secs, timed = run_command(cmd, cwd=ws, timeout=timeout, env=env)
    if code != 0 and ("Failed to connect to bus" in out or "System has not been booted" in out):
        code, out, secs, timed = run_command(["lake", *lake_args], cwd=ws, timeout=timeout, env=env)
    return code, out, secs, timed


REMOTE_SCRIPT = Path(
    "/home/gavin/.omp/plugins/node_modules/@scidonia/omp-tools/scripts/gcloud-remote.ts"
)


def remote_config() -> dict | None:
    """The worker this checkout compiles on, or `None` for a local build.

    A check never silently falls back to the local machine: an unavailable
    worker is a recorded backend error, because the local host does not have
    the memory for a swarm of elaborations.
    """
    if os.environ.get("PA_LOCAL"):
        return None
    path = ROOT / ".remote.json"
    if not path.is_file():
        return None
    try:
        cfg = load_json(path)
    except (json.JSONDecodeError, OSError):
        return None
    if not cfg.get("session") or not cfg.get("worker"):
        return None
    return cfg


def remote_invoke(cfg: dict, args: list[str], timeout: int) -> tuple[int, str, float, bool]:
    return run_command(
        ["bun", str(REMOTE_SCRIPT), *args],
        cwd=ROOT,
        timeout=timeout,
        env=os.environ.copy(),
    )


def local_check(ws: Path, module: str, checks: list[tuple[dict, str]], timeout: int):
    code, build_out, build_s, timed = run_lake(ws, ["build", "+" + module], timeout=timeout)
    outputs: dict[str, tuple[int, str, float, bool]] = {}
    if code == 0 and not timed:
        for target, rel in checks:
            outputs[target["name"]] = run_lake(
                ws, ["env", "lean", rel], timeout=timeout
            )
    return code, build_out, build_s, timed, outputs


def remote_check(
    cfg: dict,
    ws: Path,
    run_id: str,
    agent: str,
    module: str,
    checks: list[tuple[dict, str]],
    timeout: int,
):
    """Sync the workspace and run the build plus every target check on the worker.

    One tar and one remote shell carry the whole check, so a five-target problem
    is one tunnel round trip rather than six.
    """
    safe = f"{run_id}-{agent}".replace("/", "_")
    tar_name = f"pa-{safe}.tgz"
    tar_path = ws.parent / tar_name
    subprocess.run(
        ["tar", "-czf", str(tar_path), "-C", str(ws), "--exclude=.lake", "."],
        check=True,
    )
    try:
        code, out, _, timed = remote_invoke(
            cfg, ["copy", "--session", cfg["session"], "--to", str(tar_path), "/tmp/"],
            timeout=timeout,
        )
        if code != 0 or timed:
            raise RuntimeError(
                f"copy to worker failed (exit {code}{', timeout' if timed else ''}): "
                + "\n".join(out.strip().splitlines()[-8:])
            )

        rbase = f"{cfg.get('remote_root', '$HOME/pa')}/{run_id}/{agent}"
        lake = cfg.get("lake", "lake")
        # The transport collapses newlines in the command, so the whole check
        # is one `&&`/`;` line and the `cd` is in the same shell as the builds.
        parts = [
            "set -u",
            f"mkdir -p {rbase}",
            f"tar -xzf /tmp/{tar_name} -C {rbase}",
            f"cd {rbase}",
            "echo PAX_BUILD_BEGIN",
            f"( {lake} build +{module}; echo PAX_BUILD_EXIT:$? )",
        ]
        for i, (_, rel) in enumerate(checks):
            parts.append(f"echo PAX_TARGET_BEGIN:{i}")
            parts.append(f"( {lake} env lean {rel}; echo PAX_TARGET_EXIT:$? )")
        script = " && ".join(parts[:4]) + "; " + "; ".join(parts[4:])

        code, out, secs, timed = remote_invoke(
            cfg, ["run", "--session", cfg["session"], "--", script], timeout=timeout
        )
        if "PAX_BUILD_BEGIN" not in out:
            raise RuntimeError(
                f"remote check did not run (exit {code}): "
                + "\n".join(out.strip().splitlines()[-8:])
            )

        build_start = out.index("PAX_BUILD_BEGIN") + len("PAX_BUILD_BEGIN")
        build_mark = out.find("PAX_BUILD_EXIT:", build_start)
        if build_mark < 0:
            raise RuntimeError("remote check produced no build exit marker")
        build_out = out[build_start:build_mark]
        line_end = out.find("\n", build_mark)
        build_exit = int(out[build_mark + len("PAX_BUILD_EXIT:"):line_end].strip())

        outputs: dict[str, tuple[int, str, float, bool]] = {}
        for i, (target, _) in enumerate(checks):
            begin = out.find(f"PAX_TARGET_BEGIN:{i}")
            if begin < 0:
                outputs[target["name"]] = (1, "missing remote marker", 0.0, False)
                continue
            body_start = out.find("\n", begin) + 1
            exit_mark = out.find("PAX_TARGET_EXIT:", body_start)
            body = out[body_start:exit_mark] if exit_mark >= 0 else out[body_start:]
            exit_end = out.find("\n", exit_mark) if exit_mark >= 0 else -1
            exit_code = int(out[exit_mark + len("PAX_TARGET_EXIT:"):exit_end].strip()) if exit_mark >= 0 else 1
            outputs[target["name"]] = (exit_code, body, 0.0, False)
        return build_exit, build_out, secs, timed, outputs
    finally:
        tar_path.unlink(missing_ok=True)


def parse_axioms(output: str) -> list[str] | None:
    if "does not depend on any axioms" in output:
        return []
    m = re.search(r"depends on axioms:\s*\[(.*?)\]", output, re.S)
    if not m:
        return None
    body = m.group(1).strip()
    if not body:
        return []
    return [x.strip() for x in body.split(",") if x.strip()]


def target_check_source(problem: dict, target: dict) -> str:
    ns = problem["namespace"]
    mod = problem["path"].replace("/", ".")
    return (
        f"import Problems.{mod}\n"
        f"import Proofs.{mod}\n\n"
        f"example : {ns}.{target['name']} := {ns}.{target['proof']}\n"
        f"#print axioms {ns}.{target['proof']}\n"
    )


def cmd_warm(args: argparse.Namespace) -> int:
    """Populate the cached dev-shell environment once, before agents race for it."""
    env = toolchain_env()
    print(f"toolchain cached: {env.get('PATH', '').split(':')[0]}")
    return 0


def cmd_list(args: argparse.Namespace) -> int:
    manifest = load_json(ROOT / "problems" / "manifest.json")
    for p in manifest["problems"]:
        print(f"{p['id']:28s} {p['tier']:7s} targets: " + ", ".join(t["name"] for t in p["targets"]))
    return 0


def cmd_start(args: argparse.Namespace) -> int:
    run_dir = find_run(args.run)
    run = load_json(run_dir / "run.json")
    if run.get("started_at"):
        print(f"already started at {run['started_at']}")
        return 0
    run["started_at"] = utc_now()
    (run_dir / "run.json").write_text(json.dumps(run, indent=2, sort_keys=True) + "\n")
    append_event(run_dir, {
        "kind": "start", "run_id": run["run_id"], "method": run["method"],
        "ts": run["started_at"], "problems": run["problems"],
        "budget_s": run["budget_s"],
    })
    print(f"started {run['run_id']} at {run['started_at']}")
    return 0


def cmd_finish(args: argparse.Namespace) -> int:
    """Stop the clock.  A run that solved everything ends at its last check; a
    run that exhausted its budget ends at the budget."""
    run_dir = find_run(args.run)
    run = load_json(run_dir / "run.json")
    if run.get("ended_at"):
        print(f"already finished at {run['ended_at']}")
        return 0
    run["ended_at"] = utc_now()
    run["end_reason"] = args.reason
    (run_dir / "run.json").write_text(json.dumps(run, indent=2, sort_keys=True) + "\n")
    append_event(run_dir, {
        "kind": "finish", "run_id": run["run_id"], "method": run["method"],
        "ts": run["ended_at"], "reason": args.reason,
    })
    print(f"finished {run['run_id']} ({args.reason}) at {run['ended_at']}")
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    run_dir = find_run(args.run)
    run = load_json(run_dir / "run.json")
    problems = problem_map(run_dir)
    if args.problem not in problems:
        sys.exit(f"problem {args.problem!r} is not in this run")
    problem = problems[args.problem]
    ws = workspace_for(run_dir, run, args.agent)

    # A run created against a worker must not quietly become a local run if
    # the configuration disappears; the local host cannot carry a swarm.
    if run.get("compile_backend") == "remote" and not args.local and remote_config() is None:
        append_event(run_dir, {
            "kind": "check", "run_id": run["run_id"], "method": run["method"],
            "agent": args.agent, "problem": args.problem, "started": utc_now(),
            "ts": utc_now(), "duration_s": 0.0, "exit": 3,
            "backend_error": "run requires the remote worker but .remote.json is missing",
            "solved": False, "targets": {},
        })
        print("FAIL: run requires the remote worker but .remote.json is missing")
        return 3

    module = "Proofs." + problem["path"].replace("/", ".")

    # 1. The statement is immutable.  A changed statement makes every target
    #    in this problem unverifiable, so this check is fatal and loud.
    statement_path = ws / "Problems" / (problem["path"] + ".lean")
    statement_ok = (
        statement_path.is_file()
        and sha256_file(statement_path) == problem["statement_sha256"]
    )

    fatal, reports = scan_forbidden(ws / "Proofs")
    proof_lines, declarations = proof_stats(ws / "Proofs")
    t0 = time.monotonic()
    started = utc_now()
    result: dict = {
        "kind": "check", "run_id": run["run_id"], "method": run["method"],
        "agent": args.agent, "problem": args.problem, "started": started,
        "statement_ok": statement_ok, "forbidden_fatal": fatal,
        "forbidden_reported": reports, "targets": {}, "solved": False,
        "proof_lines": proof_lines, "declarations": declarations,
    }

    if not statement_ok:
        result.update(exit=2, build_ok=False, ts=utc_now(), duration_s=0.0,
                      note="statement file missing or modified")
        append_event(run_dir, result)
        print(f"FAIL {args.problem}: statement file missing or modified")
        return 2
    if fatal:
        result.update(exit=2, build_ok=False, ts=utc_now(), duration_s=0.0,
                      note="forbidden construct")
        append_event(run_dir, result)
        print("FAIL: forbidden construct(s): " + "; ".join(fatal))
        return 2

    # 2. Each target gets its own check file, so a missing proof does not hide
    #    the others and the axiom print is unambiguous.
    checks: list[tuple[dict, str]] = []
    for target in problem["targets"]:
        check_rel = Path("Check") / problem["path"] / (target["name"] + ".lean")
        check_path = ws / check_rel
        check_path.parent.mkdir(parents=True, exist_ok=True)
        check_path.write_text(target_check_source(problem, target))
        checks.append((target, str(check_rel)))

    # 3. Compile on the worker.  The local host does not have the memory for a
    #    swarm of elaborations, so a worker that cannot be reached is a loud
    #    failed check, not a quiet local fallback.
    cfg = None if args.local else remote_config()
    backend = "remote" if cfg else "local"
    result.update(backend=backend, worker=(cfg or {}).get("worker"))
    if cfg:
        try:
            code, build_out, build_s, timed_out, outputs = remote_check(
                cfg, ws, run["run_id"], args.agent, module, checks, args.timeout
            )
        except Exception as exc:  # transport failure is reported, never hidden
            result.update(exit=3, build_ok=False, ts=utc_now(),
                          duration_s=round(time.monotonic() - t0, 2),
                          backend_error=str(exc))
            append_event(run_dir, result)
            print(f"FAIL {args.problem}: remote backend: {exc}")
            return 3
    else:
        code, build_out, build_s, timed_out, outputs = local_check(
            ws, module, checks, args.timeout
        )

    result.update(build_ok=(code == 0 and not timed_out),
                  build_exit=code, build_s=round(build_s, 2),
                  build_timed_out=timed_out,
                  build_tail="\n".join(build_out.strip().splitlines()[-25:]))
    if code != 0 or timed_out:
        result.update(exit=1 if not timed_out else 124, ts=utc_now(),
                      duration_s=round(time.monotonic() - t0, 2))
        append_event(run_dir, result)
        print(f"FAIL {args.problem}: build ({'timeout' if timed_out else 'exit %d' % code})")
        tail = "\n".join(build_out.strip().splitlines()[-12:])
        if tail:
            print(tail)
        return 1

    any_ok = False
    all_ok = True
    for target, _ in checks:
        ccode, cout, cs, ctimed = outputs.get(
            target["name"], (1, "build did not produce this target", 0.0, False)
        )
        axioms = parse_axioms(cout)
        type_ok = ccode == 0 and not ctimed
        bad = [a for a in (axioms or []) if a not in ALLOWED_AXIOMS]
        ok = bool(type_ok and axioms is not None and not bad)
        result["targets"][target["name"]] = {
            "ok": ok,
            "type_ok": type_ok,
            "axioms": axioms,
            "disallowed": bad,
            "duration_s": round(cs, 2),
            "tail": "\n".join(cout.strip().splitlines()[-12:]) if not ok else "",
        }
        any_ok = any_ok or ok
        all_ok = all_ok and ok

    result.update(exit=0 if all_ok else 1, ts=utc_now(), solved=all_ok,
                  duration_s=round(time.monotonic() - t0, 2))
    if reports:
        result["note_sorries"] = reports
    append_event(run_dir, result)

    proved = sum(1 for t in result["targets"].values() if t["ok"])
    total = len(result["targets"])
    verdict = "OK" if all_ok else ("PARTIAL" if any_ok else "FAIL")
    print(f"{verdict} {args.problem} ({proved}/{total} targets, {result['duration_s']}s)")
    for name, t in result["targets"].items():
        if not t["ok"]:
            if t["axioms"] is None:
                print(f"  {name}: did not type-check against the declared target")
            elif t["disallowed"]:
                print(f"  {name}: disallowed axioms {t['disallowed']}")
            else:
                print(f"  {name}: type-check failed")
            if t["tail"]:
                print("    " + t["tail"].replace("\n", "\n    "))
    return 0 if all_ok else 1


def cmd_note(args: argparse.Namespace) -> int:
    run_dir = find_run(args.run)
    run = load_json(run_dir / "run.json")
    append_event(run_dir, {
        "kind": "note", "run_id": run["run_id"], "method": run["method"],
        "agent": args.agent, "ts": utc_now(), "text": args.text,
        "cheat": bool(args.cheat),
    })
    if args.cheat:
        print("recorded: CHEATING REPORTED")
    return 0


def cmd_status(args: argparse.Namespace) -> int:
    run_dir = find_run(args.run)
    run = load_json(run_dir / "run.json")
    problems = problem_map(run_dir)
    events = []
    ep = run_dir / "events.jsonl"
    if ep.is_file():
        events = [json.loads(line) for line in ep.read_text().splitlines() if line.strip()]
    solved: dict[str, dict] = {}
    for ev in events:
        if ev.get("kind") == "check" and ev.get("problem") in problems:
            solved.setdefault(ev["problem"], {"targets": {}, "agents": set()})
            for name, t in ev.get("targets", {}).items():
                if t.get("ok"):
                    solved[ev["problem"]]["targets"][name] = ev["agent"]
            solved[ev["problem"]]["agents"].add(ev["agent"])
    print(f"run {run['run_id']} method={run['method']} started={run.get('started_at')}")
    for pid, p in problems.items():
        if pid not in run["problems"]:
            continue
        got = solved.get(pid, {"targets": {}, "agents": set()})
        names = [t["name"] for t in p["targets"]]
        done = sum(1 for n in names if n in got["targets"])
        print(f"  {pid:28s} {done}/{len(names)} targets  agents={sorted(got['agents'])}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("warm")
    p.set_defaults(fn=cmd_warm)

    p = sub.add_parser("list")
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("start")
    p.add_argument("--run", required=True)
    p.set_defaults(fn=cmd_start)

    p = sub.add_parser("finish")
    p.add_argument("--run", required=True)
    p.add_argument("--reason", default="budget or all problems solved")
    p.set_defaults(fn=cmd_finish)

    p = sub.add_parser("check")
    p.add_argument("--run", required=True)
    p.add_argument("--agent", required=True)
    p.add_argument("--problem", required=True)
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--local", action="store_true",
                   help="compile on this host; for the harness self-test only")
    p.set_defaults(fn=cmd_check)

    p = sub.add_parser("note")
    p.add_argument("--run", required=True)
    p.add_argument("--agent", required=True)
    p.add_argument("--text", required=True)
    p.add_argument("--cheat", action="store_true")
    p.set_defaults(fn=cmd_note)

    p = sub.add_parser("status")
    p.add_argument("--run", required=True)
    p.set_defaults(fn=cmd_status)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
