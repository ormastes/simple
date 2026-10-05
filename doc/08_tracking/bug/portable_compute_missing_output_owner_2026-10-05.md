# Portable source emitter omitted its raw-output import

Status: source repair; native UNRUN.

Group 27 in `executable-batch20-buildrunner-fix1/failure-groups-first58.json`
was initially keyed by a facade warning. Its actual `[hir-fatal]` diagnostics
report unresolved `print_raw` calls in `src/app/portable_compute_emit/main.spl`.
The leaf invokes raw output repeatedly without declaring or importing it.

Import the existing `std.nogc_sync_mut.sffi.diag.print_raw` wrapper. Its runtime
owner calls `rt_print` without appending a newline. This preserves shader bytes
and marker boundaries; replacing calls with newline-printing statements would
change the emitted protocol. No new FFI or behavior is introduced.

The native integration spec invokes the real binary for WebGPU and Vulkan,
checks successful exits and nonempty delimited shader output, and verifies
unknown targets fail without emitting source markers. It requires an explicit
binary path and has no successful missing-infrastructure fallback. Native
build/run, emitted-source hashes and performance/memory measurements remain
pending in the admitted small-to-large lane. No active snapshots were changed.
