#!/bin/sh
# Core runtime sanity checks for compiler/lib changes.
# Usage:
#   sh scripts/check-core-runtime-smoke.sh [runtime_path]
# Environment:
#   SIMPLE_BINARY can also provide the runtime path.

set -eu

RUNTIME="${1:-${SIMPLE_BINARY:-bin/simple}}"
TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/simple-core-smoke.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

info() { printf '[INFO] %s\n' "$1"; }
fail() { printf '[FAIL] %s\n' "$1" >&2; }

if [ ! -x "$RUNTIME" ]; then
    fail "Runtime not executable: $RUNTIME"
    exit 1
fi

run_snippet() {
    label="$1"
    code="$2"
    expect="$3"
    out_file="$TMP_DIR/${label}.out"
    err_file="$TMP_DIR/${label}.err"

    if ! "$RUNTIME" -c "$code" >"$out_file" 2>"$err_file"; then
        fail "$label failed"
        printf '[DEBUG] stderr preview: %s\n' "$(head -c 240 "$err_file" | tr '\n' ' ')" >&2
        exit 1
    fi

    if ! grep -F "$expect" "$out_file" >/dev/null 2>&1; then
        fail "$label did not print expected output: $expect"
        printf '[DEBUG] stdout preview: %s\n' "$(head -c 240 "$out_file" | tr '\n' ' ')" >&2
        exit 1
    fi

    info "$label ok"
}

FUNCTION_CALL_CODE=$(cat <<'EOF'
fn square(x):
    x * x
print square(7)
EOF
)

CONTROL_FLOW_CODE=$(cat <<'EOF'
if true:
    print 1
else:
    print 0
EOF
)

RECURSION_CODE=$(cat <<'EOF'
fn fact(n):
    if n < 2:
        1
    else:
        n * fact(n - 1)
print fact(5)
EOF
)

info "Runtime: $RUNTIME"
"$RUNTIME" --version

run_snippet "basic-print" 'print 42' '42'
run_snippet "function-call" "$FUNCTION_CALL_CODE" '49'
run_snippet "control-flow" "$CONTROL_FLOW_CODE" '1'
run_snippet "recursion" "$RECURSION_CODE" '120'

if [ -d "test/unit/core" ]; then
    info "Running core unit tests"
    "$RUNTIME" test test/unit/core/ --timeout=120
fi

info "Core runtime smoke passed"
