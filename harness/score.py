#!/usr/bin/env python3
"""Turn a run's events into the numbers a retrospective compares.

Reads only `run.json`, `manifest.json` and `events.jsonl`.  A solve is a check
event whose every target was accepted.  An abandoned problem is unsolved at
whatever time the run ended, which is what the survival curve needs.

Usage:
  score.py --run runs/s1-...        # writes summary.json and summary.md
  score.py --all                    # writes results/method-summary.md
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def load_json(path: Path) -> dict:
    with path.open() as f:
        return json.load(f)


def parse_ts(s: str) -> datetime:
    # `datetime.isoformat()` produced these; tolerate a trailing Z.
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    return datetime.fromisoformat(s).astimezone(timezone.utc)


def run_dirs() -> list[Path]:
    root = ROOT / "runs"
    if not root.is_dir():
        return []
    return sorted(p for p in root.iterdir() if (p / "run.json").is_file())


def score_run(run_dir: Path) -> dict:
    run = load_json(run_dir / "run.json")
    manifest = {p["id"]: p for p in load_json(run_dir / "manifest.json")["problems"]}
    events: list[dict] = []
    ep = run_dir / "events.jsonl"
    if ep.is_file():
        for line in ep.read_text().splitlines():
            if line.strip():
                events.append(json.loads(line))

    start = parse_ts(run["started_at"]) if run.get("started_at") else None
    ended = parse_ts(run["ended_at"]) if run.get("ended_at") else None
    if start is None:
        return {"run_id": run["run_id"], "method": run["method"], "error": "never started"}

    checks = [e for e in events if e.get("kind") == "check"]
    notes = [e for e in events if e.get("kind") == "note"]
    last_event_ts = max((parse_ts(e["ts"]) for e in events if e.get("ts")), default=start)
    wall_end = ended or last_event_ts
    wall_s = max(0.0, (wall_end - start).total_seconds())

    # A target is green if any check accepted it.  A problem is solved when
    # every declared target is green; `first_solve_s` is the earliest check
    # that had all of them.
    per_problem: dict[str, dict] = {}
    for pid, p in manifest.items():
        if pid not in run["problems"]:
            continue
        checks_p = [e for e in checks if e.get("problem") == pid]
        target_names = [t["name"] for t in p["targets"]]
        green = {n: None for n in target_names}
        solved_at = None
        for e in checks_p:
            for n, t in e.get("targets", {}).items():
                if n in green and t.get("ok") and green[n] is None:
                    green[n] = parse_ts(e["ts"])
            if e.get("solved") and solved_at is None:
                solved_at = parse_ts(e["ts"])
        first_check = min((parse_ts(e["ts"]) for e in checks_p), default=None)
        per_problem[pid] = {
            "id": pid,
            "tier": p["tier"],
            "targets_total": len(target_names),
            "targets_proved": sum(1 for n in target_names if green[n] is not None),
            "solved": solved_at is not None,
            "solve_s": round((solved_at - start).total_seconds(), 1) if solved_at else None,
            "first_check_s": round((first_check - start).total_seconds(), 1) if first_check else None,
            "checks": len(checks_p),
            "failed_checks": sum(1 for e in checks_p if not e.get("solved")),
            "proof_lines": max((e.get("proof_lines", 0) for e in checks_p), default=0),
            "declarations": max((e.get("declarations", 0) for e in checks_p), default=0),
            "agents": sorted({e["agent"] for e in checks_p}),
            "green_by_agent": {
                n: next((e["agent"] for e in checks_p
                         if e.get("targets", {}).get(n, {}).get("ok")), None)
                for n in target_names
            },
            "target_first_green_s": {
                n: round((green[n] - start).total_seconds(), 1) if green[n] else None
                for n in target_names
            },
        }

    problems = list(per_problem.values())
    solved = [p for p in problems if p["solved"]]
    by_tier: dict[str, dict] = {}
    for p in problems:
        t = by_tier.setdefault(p["tier"], {"problems": 0, "solved": 0,
                                           "targets_total": 0, "targets_proved": 0})
        t["problems"] += 1
        t["solved"] += 1 if p["solved"] else 0
        t["targets_total"] += p["targets_total"]
        t["targets_proved"] += p["targets_proved"]
    targets_total = sum(p["targets_total"] for p in problems)
    targets_proved = sum(p["targets_proved"] for p in problems)
    hours = wall_s / 3600.0 if wall_s else 0.0
    solve_times = [p["solve_s"] for p in solved if p["solve_s"] is not None]
    first_solve_s = min(solve_times) if solve_times else None
    target_times = [
        t for p in problems for t in p.get("target_first_green_s", {}).values() if t is not None
    ]
    first_target_s = min(target_times) if target_times else None
    single_problem = len(problems) == 1
    agent_wall = run.get("agents", [])
    agent_minutes_allocated = len(agent_wall) * wall_s / 60.0
    per_agent: dict[str, dict] = {}
    for a in agent_wall:
        a_checks = [e for e in checks if e.get("agent") == a]
        ts = [parse_ts(e["ts"]) for e in a_checks]
        per_agent[a] = {
            "checks": len(a_checks),
            "failed_checks": sum(1 for e in a_checks if not e.get("solved")),
            "active_s": round((max(ts) - min(ts)).total_seconds(), 1) if len(ts) > 1 else 0.0,
            "targets": sum(1 for e in a_checks for t in e.get("targets", {}).values() if t.get("ok")),
        }

    cheating = [e for e in notes if e.get("cheat")]
    relay_turns = sum(1 for e in notes if e.get("agent") == "conductor")
    check_durations = [e.get("duration_s", 0.0) for e in checks if e.get("duration_s") is not None]

    summary = {
        "run_id": run["run_id"],
        "void": run.get("void", False),
        "void_reason": run.get("void_reason"),
        "method": run["method"],
        "method_name": run.get("method_name"),
        "budget_s": run["budget_s"],
        "compile_backend": run.get("compile_backend"),
        "worker": run.get("worker"),
        "started_at": run["started_at"],
        "ended_at": run.get("ended_at"),
        "end_reason": run.get("end_reason"),
        "wall_clock_s": round(wall_s, 1),
        "wall_clock_capped_by_budget": wall_s >= run["budget_s"] - 1,
        "agents": agent_wall,
        "problems": problems,
        "totals": {
            "problems": len(problems),
            "solved": len(solved),
            "solve_fraction": round(len(solved) / len(problems), 3) if problems else 0.0,
            "targets_total": targets_total,
            "targets_proved": targets_proved,
            "target_fraction": round(targets_proved / targets_total, 3) if targets_total else 0.0,
            "checks": len(checks),
            "failed_checks": sum(1 for e in checks if not e.get("solved")),
            "declarations": sum(p.get("declarations", 0) for p in problems),
            "proof_lines": sum(p.get("proof_lines", 0) for p in problems),
            "relay_turns": relay_turns,
            "checks_per_solve": round(len(checks) / len(solved), 2) if solved else None,
            "failed_checks_per_solve": round(
                sum(1 for e in checks if not e.get("solved")) / len(solved), 2
            ) if solved else None,
            "median_check_s": round(statistics.median(check_durations), 3) if check_durations else None,
            "problems_per_hour": round(len(solved) / hours, 2) if hours else None,
            "targets_per_hour": round(targets_proved / hours, 2) if hours else None,
            # For a one-problem comparison the headline is the first green
            # check, not the moment the conductor got round to stopping the
            # clock; the latter includes report-writing after the solve.
            "single_problem": single_problem,
            "first_target_s": first_target_s,
            "first_solve_s": first_solve_s,
            "solve_rate_per_hour": round(3600.0 / first_solve_s, 2) if first_solve_s else None,
            "agent_minutes_by_solve_s": round(
                len(agent_wall) * first_solve_s / 60.0, 1
            ) if first_solve_s else None,
            "minutes_per_solved_problem": round(wall_s / 60.0 / len(solved), 2) if solved else None,
            "agent_minutes_allocated": round(agent_minutes_allocated, 1),
            "agent_minutes_per_solved_problem": round(agent_minutes_allocated / len(solved), 1) if solved else None,
        },
        "by_tier": by_tier,
        "per_agent": per_agent,
        "cheating_reported": cheating,
        "notes": [{"agent": n["agent"], "ts": n["ts"], "text": n.get("text", "")} for n in notes],
    }
    return summary


def write_summary(run_dir: Path, summary: dict) -> None:
    (run_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    t = summary.get("totals", {})
    lines = [
        f"# {summary['run_id']} — {summary['method']}",
        "",
        f"method: {summary.get('method_name')} · agents: {len(summary.get('agents', []))} · "
        f"budget: {summary['budget_s']}s · wall clock: {summary['wall_clock_s']}s",
        "",
        "| problem | tier | targets | solved | solve s | checks | agents |",
        "| --- | --- | ---: | --- | ---: | ---: | --- |",
    ]
    for p in summary["problems"]:
        lines.append(
            f"| {p['id']} | {p['tier']} | {p['targets_proved']}/{p['targets_total']} | "
            f"{'yes' if p['solved'] else 'no'} | {p['solve_s'] if p['solve_s'] is not None else '—'} | "
            f"{p['checks']} | {', '.join(p['agents'])} |"
        )
    lines += [
        "",
        f"solved **{t.get('solved')}/{t.get('problems')}** · "
        f"targets **{t.get('targets_proved')}/{t.get('targets_total')}** · "
        f"**{t.get('problems_per_hour')}** problems/hour · "
        f"{t.get('agent_minutes_per_solved_problem')} agent-min/solve",
        "",
        f"checks: {t.get('checks')} ({t.get('failed_checks')} failed, "
        f"median {t.get('median_check_s')}s) · cheating reports: {len(summary.get('cheating_reported', []))}",
        "",
    ]
    (run_dir / "summary.md").write_text("\n".join(lines))


def compare(run_dirs_: list[Path]) -> str:
    rows = []
    for d in run_dirs_:
        sp = d / "summary.json"
        if not sp.is_file():
            continue
        s = load_json(sp)
        if s.get("void"):
            continue
        t = s.get("totals", {})
        rows.append({
            "run": s["run_id"],
            "method": s["method"],
            "agents": len(s.get("agents", [])),
            "backend": s.get("compile_backend") or "local",
            "solved": f"{t.get('solved')}/{t.get('problems')}",
            "targets": f"{t.get('targets_proved')}/{t.get('targets_total')}",
            "wall_s": s["wall_clock_s"],
            "probs_per_h": (t.get("solve_rate_per_hour")
                            if t.get("single_problem") else t.get("problems_per_hour")),
            "agent_min_per_solve": (t.get("agent_minutes_by_solve_s")
                                    if t.get("single_problem")
                                    else t.get("agent_minutes_per_solved_problem")),
            "checks_per_solve": t.get("checks_per_solve"),
            "cheat": len(s.get("cheating_reported", [])),
        })
    lines = [
        "# Method comparison",
        "",
        "(Generated from each run's summary.json. Problems unsolved at the budget are counted as unsolved; "
        "a run with a cheating report is marked and is not comparable.)",
        "",
        "| run | method | agents | compile | solved | targets | wall s | problems/h | agent-min/solve | checks/solve | cheat |",
        "| --- | --- | ---: | --- | --- | --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for r in rows:
        lines.append(
            f"| {r['run']} | {r['method']} | {r['agents']} | {r['backend']} | {r['solved']} | {r['targets']} | "
            f"{r['wall_s']} | {r['probs_per_h']} | {r['agent_min_per_solve']} | "
            f"{r['checks_per_solve']} | {r['cheat']} |"
        )
    lines.append("")
    (ROOT / "results").mkdir(exist_ok=True)
    (ROOT / "results" / "method-summary.md").write_text("\n".join(lines))
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", action="append", default=[])
    ap.add_argument("--all", action="store_true")
    args = ap.parse_args()
    if args.all:
        for d in run_dirs():
            s = score_run(d)
            if "error" not in s:
                write_summary(d, s)
        print(compare(run_dirs()))
    else:
        if not args.run:
            sys.exit("give --run DIR (repeatable) or --all")
        for r in args.run:
            d = Path(r)
            if not d.is_absolute():
                by_id = ROOT / "runs" / d
                d = (by_id if by_id.is_dir() else (ROOT / d)).resolve()
            s = score_run(d)
            if "error" in s:
                print(f"{d.name}: {s['error']}")
                continue
            write_summary(d, s)
            print((d / "summary.md").read_text())
    return 0


if __name__ == "__main__":
    sys.exit(main())
