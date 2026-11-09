# stage3_fdwalk Darwin syntax shim

Minimal header stubs so `clang --target=arm64-apple-macos -fsyntax-only` can
check `src/runtime/tools/stage3_fdwalk.c` on a host WITHOUT a macOS SDK
(Windows/Linux CI). Used only by `scripts/check/check-stage3-fdwalk-helper.shs`
when `xcrun --show-sdk-path` is unavailable.

What it proves: the helper's own C is well-formed for the `__APPLE__` branch
(F_GETPATH / lstat / stat / execve path) and uses the POSIX surface declared
here consistently. What it does NOT prove: conformance with the real macOS SDK
headers. That is the Darwin spec's job
(`test/01_unit/bootstrap/stage3_fdwalk_darwin_spec.shs`), run natively.
