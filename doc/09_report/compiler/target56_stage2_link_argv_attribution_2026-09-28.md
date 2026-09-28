# Target 5/6 Stage2 full CLI link attribution

Status: diagnosis; no Stage2 matrix or Target 5/6 qualification PASS.

The admitted pre-rebase Stage2 compiler's in-process matrix stopped at the
full CLI link after 1,828 seconds and 3,687,032 KiB max RSS. Its linker log
lists 178 distinct unresolved symbols. The selected `host-gpu` runtime path
is an immutable phase-2 capsule with SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.

To identify selected link inputs without repeating that 30-minute build,
a 37-file no-stub native probe used the same Stage2 compiler, `host-gpu`
bundle, and runtime path under `strace -f -e execve`. Its successful
`clang++` invocation passed a generated
`host_gpu_core_c_runtime/libsimple_runtime.a` and the capsule's
`deps/libspl_hosted_runtime-*.rlib`; it did not pass
`libsimple_native_all.a`. The trace is retained at
`build/mini_builds/target56_dynlib_probe/trace_link_execve.log`, and the
probe build log is beside it. Source confirms this is intentional selection:
`selected_runtime_library` leaves `HostGpu` without a native-all candidate,
and `link_objects` adds the core-C archive plus hosted rlib instead. This
focused trace establishes the bundle shape, not the exact argv of the failed
full CLI invocation.

The failed full CLI build retained its generated core-C archive. Comparing
`nm -g --defined-only` against the 178 names in its linker log gives:

| Archive | Unresolved names it defines |
|---|---:|
| Selected generated core-C archive | 0 |
| Selected hosted rlib | 0 exact unmangled names |
| Frozen native-all archive, **not selected** | 117 |

The other 61 are 25 SQLite, 18 SDL, six other `rt_*` symbols (ARM array and
hosted safe-artifact helpers), and 12 others including Rust standard-library
symbols and two unresolved Simple helpers. The core-C provider cannot satisfy
the full CLI closure as currently reached. Merely appending native-all would
still leave missing provider families and would change the optional-provider
loading policy; it is a diagnostic option, not a Target 5 fix.

One of the two Simple helper names, `_text_list_contains`, does resolve and
execute in a focused two-file, no-stub native build from an explicit
`driver_compile_vhdl_util` import. Its 45 KB probe prints `true`; logs are in
`build/mini_builds/target56_link_helper_probe/`. The full-closure failure is
therefore not evidence that the helper is absent. `driver_compile_vhdl_expr`
already documents an import resolver defect that varies with full closure
shape and uses a local decimal-digit workaround. This needs a resolver fix or
full-closure qualification, not another duplicate helper.

Next implementation boundary: make the full CLI's reached optional modules
explicit and route first use through admitted provider artifacts. Keep the
minimal core link free of those providers. Then supply genuinely required
Stage2 test-tool providers through an explicit, receipt-bound selection,
resolve the two Simple helpers, and rerun the five-row matrix. Stage4 and the
matched size/startup and compile time/RSS cohorts remain separate gates.
