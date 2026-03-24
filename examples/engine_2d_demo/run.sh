#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

run_demo() {
    local bin_path="$1"
    shift
    "$bin_path" run examples/engine_2d_demo/main.spl "$@"
}

if run_demo bin/simple_native "$@"; then
    exit 0
else
    status=$?
fi

if [ "$status" -eq 139 ]; then
    echo "error: bin/simple_native segfaulted while handling 'run'." >&2
    echo "The crash reproduces on a trivial hello-world program, so the blocker is" >&2
    echo "in the current compiler-driver runtime, not specific to engine_2d_demo." >&2
fi

if run_demo bin/simple_stage4 "$@"; then
    exit 0
else
    status=$?
fi

if [ "$status" -eq 139 ]; then
    echo "error: bin/simple_stage4 also segfaulted in the generic 'run' path." >&2
fi

exit "$status"
