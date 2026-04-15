#!/usr/bin/env bash
# build_rust_hello_simpleos.sh — Phase-3 step-4 proof: cross-compile
# examples/simpleos_hello_rs/ to x86_64-unknown-simpleos and produce an
# ELF with a `_start` symbol linked against libsimpleos_c.a.
#
# Why out-of-tree: the in-tree src/compiler_rust/ workspace pins a
# vendored crate set (IF-10) that includes 11 edition-2024 crates
# (`abfall`, `compiler_builtins`, etc.). Cargo eagerly parses every
# vendored manifest, and nightly-2024-09-01 (cargo 1.82) cannot parse
# edition-2024. Newer nightlies parse edition-2024 but their `proc_macro`
# rustlib imports `rustc-literal-escaper` which is not in vendor/.
#
# This script sidesteps the pin dance entirely by staging hello_rs into
# a temp dir with a dedicated empty CARGO_HOME, so cargo falls back to
# crates.io for compiler_builtins (v0.1.123, edition-2021 compatible)
# and never touches the project vendor tree.
#
# Produces: $STAGE/target/target/release/hello_rs (ELF, _start symbol).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC_DIR="$REPO_ROOT/examples/simpleos_hello_rs"
TARGET_JSON_SRC="$REPO_ROOT/src/os/toolchain/rust/x86_64-unknown-simpleos.json"
SIMPLEOS_SYSROOT="${SIMPLEOS_SYSROOT:-$REPO_ROOT/build/os/sysroot}"
NIGHTLY_PIN="${NIGHTLY_PIN:-nightly-2024-09-01}"
STAGE="${STAGE:-/tmp/hello_rs_simpleos}"

[ -f "$SIMPLEOS_SYSROOT/lib/libsimpleos_c.a" ] || {
    echo "error: $SIMPLEOS_SYSROOT/lib/libsimpleos_c.a missing"
    echo "  Build it via: make -C $REPO_ROOT/src/os/libc"
    exit 2
}

rustup toolchain list 2>/dev/null | grep -q "$NIGHTLY_PIN" || {
    echo "Installing $NIGHTLY_PIN ..."
    rustup toolchain install "$NIGHTLY_PIN" --profile minimal --component rust-src
}

echo "[stage] $STAGE"
rm -rf "$STAGE"
cp -r "$SRC_DIR" "$STAGE"

# Patch target JSON in place: add -L to pre-link-args for libsimpleos_c.
python3 - "$TARGET_JSON_SRC" "$STAGE/target.json" "$SIMPLEOS_SYSROOT/lib" <<'PY'
import json, sys
src, dst, libdir = sys.argv[1], sys.argv[2], sys.argv[3]
t = json.load(open(src))
args = t.setdefault("pre-link-args", {}).setdefault("gnu-lld-cc", [])
flag = f"-L{libdir}"
if flag not in args:
    args.append(flag)
json.dump(t, open(dst, "w"), indent=4)
PY

echo "[build] cargo +$NIGHTLY_PIN ..."
env -i HOME="$HOME" PATH="$PATH" CARGO_HOME="$STAGE/.cargo_clean" \
    cargo "+$NIGHTLY_PIN" build --release \
        --manifest-path "$STAGE/Cargo.toml" \
        --target "$STAGE/target.json" \
        -Z build-std=core,compiler_builtins \
        -Z build-std-features=compiler-builtins-mem

ARTIFACT="$STAGE/target/target/release/hello_rs"
[ -f "$ARTIFACT" ] || { echo "error: artifact missing"; exit 3; }

echo ""
echo "==> OK: $ARTIFACT"
"$REPO_ROOT/build/os/llvm/cross-x86_64/bin/llvm-nm" "$ARTIFACT" | grep " _start" || {
    echo "error: no _start symbol"; exit 4;
}
ls -la "$ARTIFACT"
