#!/usr/bin/env bash
# install_compiler_rt_simpleos.sh — Install compiler-rt builtins archive into
# the SimpleOS sysroot resource-dir so clang auto-finds it for
# -target x86_64-unknown-simpleos without extra linker flags.
#
# Source:  build/os/llvm/cross-x86_64/lib/clang/20/lib/x86_64-unknown-simpleos/libclang_rt.builtins.a
# Dest:    build/os/sysroot/lib/clang/20/lib/x86_64-unknown-simpleos/libclang_rt.builtins.a

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

SRC="$REPO_ROOT/build/os/llvm/cross-x86_64/lib/clang/20/lib/x86_64-unknown-simpleos/libclang_rt.builtins.a"
DST_DIR="$REPO_ROOT/build/os/sysroot/lib/clang/20/lib/x86_64-unknown-simpleos"
DST="$DST_DIR/libclang_rt.builtins.a"

[ -f "$SRC" ] || {
    echo "error: source archive not found: $SRC"
    echo "  Build it via: W4-A1 compiler-rt bootstrap (scripts/build_compiler_rt_simpleos.sh)"
    exit 2
}

mkdir -p "$DST_DIR"
cp "$SRC" "$DST"

echo "==> installed $DST"
echo "    size: $(ls -lh "$DST" | awk '{print $5}')"
