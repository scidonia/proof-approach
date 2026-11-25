#!/usr/bin/env bash
# Exercise the harness's accept and reject paths against a throwaway run.
#
#   bash harness/selftest.sh          # cleans up
#   KEEP=1 bash harness/selftest.sh   # leaves runs/selftest-* for inspection
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUN="selftest-$(date +%s)"
WS="$ROOT/runs/$RUN/agents/a1/workspace"
PASS=0
FAIL=0

cleanup() {
  if [ "${KEEP:-0}" != "1" ]; then
    rm -rf "$ROOT/runs/$RUN"
  else
    echo "kept $ROOT/runs/$RUN"
  fi
}
trap cleanup EXIT

check() {
  local name="$1" expected="$2" needle="$3"
  shift 3
  set +e
  local out
  out="$("$@" 2>&1)"
  local code=$?
  set -e
  if [ "$code" -eq "$expected" ] && grep -q -- "$needle" <<<"$out"; then
    echo "ok   $name"
    PASS=$((PASS + 1))
  else
    echo "FAIL $name (exit $code, expected $expected, wanted '$needle')"
    echo "$out" | tail -20
    FAIL=$((FAIL + 1))
  fi
}

proof() {
  cat >"$WS/Proofs/Smoke/Arithmetic.lean"
}

python3 "$ROOT/harness/new_run.py" --method S0 --tier smoke --budget-s 300 \
  --run-id "$RUN" >/dev/null
python3 "$ROOT/harness/pa.py" start --run "$RUN" >/dev/null

proof <<'EOF'
import Problems.Smoke.Arithmetic
namespace Problems.Smoke.Arithmetic
theorem add_zero_proof : add_zero := by intro n; exact Nat.add_zero n
theorem add_comm_proof : add_comm := by intro a b; exact Nat.add_comm a b
theorem one_plus_one_proof : one_plus_one := by decide
end Problems.Smoke.Arithmetic
EOF
check "green proof accepted" 0 "OK smoke/arithmetic" \
  python3 "$ROOT/harness/pa.py" check --run "$RUN" --agent a1 --problem smoke/arithmetic --local

proof <<'EOF'
import Problems.Smoke.Arithmetic
namespace Problems.Smoke.Arithmetic
theorem add_zero_proof : add_zero := by sorry
theorem add_comm_proof : add_comm := by intro a b; exact Nat.add_comm a b
theorem one_plus_one_proof : one_plus_one := by decide
end Problems.Smoke.Arithmetic
EOF
check "sorry rejected" 1 "sorryAx" \
  python3 "$ROOT/harness/pa.py" check --run "$RUN" --agent a1 --problem smoke/arithmetic --local

proof <<'EOF'
import Problems.Smoke.Arithmetic
namespace Problems.Smoke.Arithmetic
theorem add_zero_proof : True := trivial
theorem add_comm_proof : add_comm := by intro a b; exact Nat.add_comm a b
theorem one_plus_one_proof : one_plus_one := by decide
end Problems.Smoke.Arithmetic
EOF
check "weakened statement rejected" 1 "type-check failed" \
  python3 "$ROOT/harness/pa.py" check --run "$RUN" --agent a1 --problem smoke/arithmetic --local

proof <<'EOF'
import Problems.Smoke.Arithmetic
namespace Problems.Smoke.Arithmetic
theorem add_zero_proof : add_zero := by intro n; exact Nat.add_zero n
theorem add_comm_proof : add_comm := by intro a b; exact Nat.add_comm a b
theorem one_plus_one_proof : one_plus_one := by native_decide
end Problems.Smoke.Arithmetic
EOF
check "native_decide rejected" 2 "native_decide" \
  python3 "$ROOT/harness/pa.py" check --run "$RUN" --agent a1 --problem smoke/arithmetic --local

proof <<'EOF'
import Problems.Smoke.Arithmetic
namespace Problems.Smoke.Arithmetic
axiom cheat : add_zero
theorem add_zero_proof : add_zero := cheat
theorem add_comm_proof : add_comm := by intro a b; exact Nat.add_comm a b
theorem one_plus_one_proof : one_plus_one := by decide
end Problems.Smoke.Arithmetic
EOF
check "axiom rejected" 2 "forbidden construct" \
  python3 "$ROOT/harness/pa.py" check --run "$RUN" --agent a1 --problem smoke/arithmetic --local

proof <<'EOF'
import Problems.Smoke.Arithmetic
namespace Problems.Smoke.Arithmetic
theorem add_zero_proof : add_zero := by intro n; exact Nat.add_zero n
theorem add_comm_proof : add_comm := by intro a b; exact Nat.add_comm a b
theorem one_plus_one_proof : one_plus_one := by decide
end Problems.Smoke.Arithmetic
EOF
printf '\n-- changed statement\n' >>"$WS/Problems/Smoke/Arithmetic.lean"
check "changed statement rejected" 2 "statement file missing or modified" \
  python3 "$ROOT/harness/pa.py" check --run "$RUN" --agent a1 --problem smoke/arithmetic --local

python3 "$ROOT/harness/pa.py" finish --run "$RUN" --reason "selftest" >/dev/null
python3 "$ROOT/harness/score.py" --run "$RUN" >/dev/null
if [ -f "$ROOT/runs/$RUN/summary.json" ]; then
  echo "ok   scorer wrote summary.json"
  PASS=$((PASS + 1))
else
  echo "FAIL scorer wrote no summary.json"
  FAIL=$((FAIL + 1))
fi

echo
echo "$PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ]
