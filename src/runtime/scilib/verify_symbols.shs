#!/bin/sh
set -eu

if [ "$#" -lt 2 ]; then
    echo "usage: $0 MOCK_SHIM OTHER_SHIM..." >&2
    exit 2
fi

MOCK_SHIM="$1"
shift

if [ ! -f "$MOCK_SHIM" ]; then
    echo "missing_mock_shim=$MOCK_SHIM" >&2
    exit 1
fi

TMP_DIR="${TMPDIR:-/tmp}/simple_scilib_symbols.$$"
mkdir -p "$TMP_DIR"
trap 'rm -rf "$TMP_DIR"' EXIT HUP INT TERM

mock_symbols="$TMP_DIR/mock.symbols"
nm -D "$MOCK_SHIM" | awk '/ T rt_/ {print $3}' | sort >"$mock_symbols"

if [ ! -s "$mock_symbols" ]; then
    echo "mock_symbols_empty=$MOCK_SHIM" >&2
    exit 1
fi

status=0
for shim in "$@"; do
    if [ ! -f "$shim" ]; then
        echo "SKIP missing $shim"
        continue
    fi
    shim_symbols="$TMP_DIR/$(basename "$shim").symbols"
    nm -D "$shim" | awk '/ T rt_/ {print $3}' | sort >"$shim_symbols"
    if diff -u "$mock_symbols" "$shim_symbols" >/dev/null; then
        echo "OK $shim"
    else
        echo "SYMBOL_MISMATCH $shim" >&2
        diff -u "$mock_symbols" "$shim_symbols" >&2 || true
        status=1
    fi
done

exit "$status"
