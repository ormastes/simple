# Stage2 full CLI link reaches optional runtime symbols outside host-gpu core

Status: OPEN; Stage2 compiler-test matrix FAIL. This is a separate blocker
after the current-source Stage2 native build, positional hello-world smoke,
struct/runtime capability proof, and focused owned-device probe passed.

The in-process matrix used the admitted compiler and verified runtime capsule
with SHA-256 `d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
`compiler_version` passed. `compiler_cli_build` failed after 1,828 seconds,
with max RSS 3,687,032 KiB. The test runner build was blocked, and the three
compiler/interpreter/loader test rows were unsupported without the CLI. The
authoritative `summary.env` reports `overall=FAIL`.

The CLI command selected `--runtime-bundle host-gpu` and compiled all of
`src/compiler`, `src/app`, and `src/lib` under entry closure. The linker then
reported many missing optional symbols, including `rt_cuda_*`, `rt_rocm_*`,
`rt_vulkan_*`, `rt_metal_*`, `rt_sqlite_*`, and `rt_sdl_*`. It also reported
undeclared `_editor_markdown_replace_line`, `_text_list_contains`, and Rust
runtime symbols. The link failure does not by itself prove those symbols are
absent from the capsule: `nm` finds `rt_cuda_init`,
`rt_vulkan_fence_submission_supported`, `rt_rocm_device_count`, and
`rt_metal_init` defined in the frozen `libsimple_native_all.a`, while this
archive does not define `rt_sqlite_open` or `rt_sdl_create_window`. The
linker's actual archive arguments and ordering still need attribution. The
log says the selected core lane intentionally limits its ABI. This result
does not undo the focused runtime probe.

Evidence:
`build/bootstrap-target56/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env`
and its `logs/compiler_cli_build.log`; the rejection is in the sibling
`rejection.env`.

Next: capture the actual linker argv, classify missing symbols against the
selected archives, and identify why the full CLI entry closure reaches
optional modules and lenient unresolved globals. Then make the closure exact
and supply any genuinely required providers through an admitted runtime lane.
Do not add fake symbols or silently expand the core ABI. Re-run the matrix
only after that source/selection change; this 1,828-second failure is the
baseline, not a passing Stage2 verification.
