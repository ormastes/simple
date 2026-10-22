# Stale macos-arm64 Simple test runner reports a false PASS

Status: OPEN — gate trustworthiness; found 2026-09-26 while verifying the selected C/N2 rendering lane.

`bin/release/macos-arm64/simple` is an April 11 binary (reports `Simple v1.0.0-beta.14`, test runner v0.9.5). A temporary spec containing `expect(1).to_equal(2)` was selected explicitly with `simple test <path> --mode=interpreter`. The runner reported one passed test, zero failures and exit code 0 in 17 ms. The temporary spec was removed after the observation. This is a deterministic false green for that binary; no rendering test result from it is admissible.

The same negative control was attempted with the July 25 `bin/release/aarch64-apple-darwin/simple` (runner v0.8.1), including a variant importing `common.ui.draw_ir` under the unit-test tree. Both runs stopped before the assertion at a clean source parse error in `src/lib/nogc_sync_mut/io/process_ops.spl` (`expected expression, found Colon`). That binary therefore has no admitted negative-control result either.

The isolated current bootstrap attempt later terminated with exit code 126:
its native-build worker tried to execute
`/private/tmp/simple_2d_verifier_20260926/bin/simple.exe` on macOS. `file`
identifies that artifact as a `PE32+` x86-64 Windows executable. This is a
host/target artifact selection failure, not an admitted test runner. The
earlier generic “parse-shard killed — check OOM” message did not establish
memory exhaustion; `memory_pressure -Q` reported 89% system-wide free and
`vm_stat` reported zero throttled pages at the time of inspection.

Impact: withdraw the apparent provider 5/5, final-output pixels 5/5 and selected system spec 1/1 results produced by `macos-arm64/simple`. The focused fractional DrawIR 2/2 and UiIr 8/8 reported by `aarch64-apple-darwin/simple` remain provisional until a current self-hosted runner executes a failing negative control and then the focused specs. The isolated attempt supplied no such runner. Do not resolve this issue from a green summary alone.

Related history: `test_runner_masks_child_and_expectation_failures_2026-07-02.md` found and later failed to reproduce a similar symptom on a different binary; `test_runner_explicit_empty_selection_false_green_2026-07-24.md` tracks another false-green path. A fix needs a fresh current self-hosted binary and a regression spec that asserts a deliberately false matcher yields nonzero exit and a failed case count.

## Isolated bootstrap worker selection

The isolated clone has a tracked `bin/simple.exe` that is a Windows PE file
and has no `bin/simple`. In `src/app/cli/native_build_main.spl`,
`resolve_simple_binary()` checks `SIMPLE_BINARY`, `SIMPLE_BIN`, and
`self_exe()`, then chooses any existing `bin/simple.exe` before `bin/simple`
without checking the host. Source entrypoints expose the `.spl` path as
`argv[0]`; macOS lacks `/proc`, and the remaining `ps` probes returned
`operation not permitted` in this sandbox. The worker guard accepts a
nonempty existing file, so the PE reached process execution and exited 126.

An isolated bootstrap retry can set `SIMPLE_BINARY` to the absolute path of
its runnable bootstrap seed for worker spawning. The durable source fix is
host-aware worker selection that refuses a Windows PE on macOS and reports
no runnable worker when appropriate. Verify with a negative control where a
PE `bin/simple.exe` is present and `bin/simple` is absent, then require a
current macOS self-hosted runner to fail a deliberately false matcher before
re-running rendering specs. `native_build_main.spl` is currently dirty in a
separate lane; this report does not fold that work into the rendering lane.

## Final isolated verifier attempt

The third bounded build attempt used the absolute Mach-O bootstrap seed via
`SIMPLE_BINARY` and `SIMPLE_BIN` in the isolated clone. The PE worker-selection
failure did not recur. Code generation produced an object archive, but the
macOS arm64 link exited 1: the selected `core-c-bootstrap` lane lacks
`_rt_vulkan_*` and `_rt_cuda_*` symbols pulled into the test-runner closure.
The terminal log is
`/private/tmp/simple_2d_verifier_20260926/build/mini_builds/renderdoc_test_runner.log`;
`renderdoc_test_runner.exit` records `native_build_exit=1`. The linker reports
`symbol(s) not found for architecture arm64`; no verifier executable or
negative-control result exists. This is a linker/lane admission problem, not
evidence of memory exhaustion.

The repository's three-cycle verify/fix cap is now reached for this verifier
build. Do not retry it in this session. A later scoped fix must make the test
runner closure select a supported native GPU-symbol lane or exclude GPU-only
modules from that closure, then build a current self-hosted runner and prove
the false-matcher control fails before treating rendering specs as evidence.

## 2026-09-27 Mac continuation

The September 18 `bin/release/aarch64-apple-darwin-macho/simple` was given one
bounded interpreter-mode negative control at
`/private/tmp/simple_2d_negative_control_20260927_spec.spl` containing
`expect(1).to_equal(2)`. It selected one file, then exited `-11` during setup
after `cover-check: 0ms`, before reporting a case result. It is not a trusted
replacement runner. No rendering spec was retried with it.
