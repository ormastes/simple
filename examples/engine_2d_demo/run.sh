#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

rust_driver="src/compiler_rust/target/debug/simple"

if [ ! -x "$rust_driver" ]; then
    echo "building Rust driver..." >&2
    cargo build --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple >&2
fi

echo "checking new 2D engine demo with Rust driver..." >&2
set +e
"$rust_driver" examples/engine_2d_demo/main.spl "$@"
status=$?
set -e

if [ "$status" -eq 0 ]; then
    exit 0
fi

echo "error: the new 2D engine demo is still not runnable end-to-end in this checkout." >&2
echo "current blockers:" >&2
echo "  1. the Rust driver has no live rt_winit_* window runtime" >&2
echo "  2. the engine still depends on rt_rapier2d_* physics runtime" >&2
echo "  3. self-hosted bin/simple_native still segfaults in generic run/check paths" >&2
echo "the launcher now reports those gaps directly instead of claiming a connected path." >&2
exit "$status"
