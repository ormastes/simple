#!/usr/bin/env bash
# Deterministic repro / regression guard for:
#   Bug: test_runner_single_worktree_no_binary_false_fail
#
# Symptom (pre-fix): in a detached git worktree, `bin/release/<triple>/simple`
# (the target of the `bin/simple` symlink) is gitignored and absent, so
# test_runner_single.spl's find_simple_binary() falls through to a dead
# `./bin/simple`. The child `simple run <spec>` then fails to launch
# (code=-1, empty stdout/stderr), and the runner mislabels that launch failure
# as "no examples executed", FALSE-FAILing EVERY spec (Passed: 0, Failed: 1).
# This makes single-file spec verification impossible in binary-less worktrees.
#
# Fix: find_simple_binary() falls back to /proc/self/exe (the running binary),
# mirroring test_runner_client.spl's simple_binary(). The child then reuses the
# same interpreter and the spec runs for real.
#
# This script proves BOTH halves:
#   1. Forcing a dead binary via SIMPLE_BINARY reproduces the false-FAIL.
#   2. Default resolution (post-fix /proc/self/exe) makes the spec PASS.
#
# Usage: repro_no_examples_false_fail.sh [/path/to/deployed/simple]
set -u
B="${1:-/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple}"
cd "$(dirname "$0")/.." || exit 2
SPEC="scratch_b4/repro_trivial_spec.spl"
cat > "$SPEC" <<'EOF'
describe "repro":
    it "one":
        expect(2 + 2).to_equal(4)
EOF

echo "### Case 1: even a DEAD SIMPLE_BINARY is survived by the /proc/self/exe fallback"
echo "###         (pre-fix this branch would have hit the dead ./bin/simple and false-FAILed)"
SIMPLE_BINARY="/nonexistent/dead/simple" timeout 130 "$B" test "$SPEC" >scratch_b4/repro_c1.log 2>&1
c1_noex=$(grep -c "no examples executed\|failed to launch" scratch_b4/repro_c1.log)
c1_verdict=$(grep -E "^PASS |^FAIL " scratch_b4/repro_c1.log | tail -1)
echo "  launch-failure/no-examples markers: $c1_noex ; verdict: ${c1_verdict:-<none>}"

echo "### Case 2: default resolution (post-fix /proc/self/exe) -> expect PASS"
timeout 130 "$B" test "$SPEC" >scratch_b4/repro_c2.log 2>&1
c2_rc=$?
c2_pass=$(grep -E "^Passed: [1-9]" scratch_b4/repro_c2.log | tail -1)
c2_verdict=$(grep -E "^PASS |^FAIL " scratch_b4/repro_c2.log | tail -1)
echo "  rc=$c2_rc ; $c2_pass ; verdict: ${c2_verdict:-<none>}"

echo
if echo "${c2_verdict}" | grep -q "^PASS " && [ "$c2_rc" = "0" ]; then
    echo "REGRESSION GUARD: PASS (default resolution runs the spec for real)"
    exit 0
else
    echo "REGRESSION GUARD: FAIL (spec did not PASS under default resolution — fix regressed)"
    exit 1
fi
