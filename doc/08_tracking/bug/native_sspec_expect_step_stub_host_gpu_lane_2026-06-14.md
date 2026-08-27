# Native SSpec host-GPU lane process SFFI crash

## Status

Fixed locally. The native SSpec `expect`/`step` unresolved-symbol blocker is
fixed: native preprocessed specs now link without generating `expect` or
`step` stubs, and minimal native specs for `step()` plus helper-function
`expect(...)` pass.

The native `rt_process_run` crash is fixed in the current checkout by aligning
the Cranelift/native C-runtime ABI for process, file-write, and directory
creation calls, and by updating `src/runtime/runtime_native.c` so
`rt_process_run` consumes and returns tagged `rt_array_*` values instead of
legacy `spl_array_*` values. The local `src/runtime/libsimple_runtime.a`
archive was regenerated from the updated `runtime_native.c`; the archive itself
is generated/untracked in this checkout.

## Evidence

Command:

```sh
SIMPLE_LIB=src bin/simple test --mode=native --clean test/03_system/feature/language/host_gpu_lane_spec.spl
```

Original observed result on 2026-06-14:

- Native mode links a temporary ELF.
- `SIMPLE_DUMP_STUBS` is empty after the runner preprocessor fix.
- Direct execution of the generated ELF exits `139`.
- A minimized native SSpec using `rt_process_run("/bin/sh", ["-c", "true"])`
  also exits `139`, while minimized `step()` and helper-`expect(...)` specs pass.

Related positive evidence:

- `SIMPLE_LIB=src bin/simple test test/03_system/feature/language/host_gpu_lane_spec.spl --mode=interpreter --clean` passes.
- `SIMPLE_LIB=src bin/simple test test/03_system/feature/language/host_gpu_event_path_spec.spl --mode=interpreter --clean` passes.
- `SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test --mode=native --force-rebuild --clean /tmp/process_run_native_spec.spl` passes.
- `SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test --mode=native --force-rebuild --clean test/03_system/feature/language/host_gpu_lane_spec.spl` passes: 7 scenarios.
- `SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test --mode=native --force-rebuild --clean test/03_system/feature/language/host_gpu_event_path_spec.spl` passes: 3 scenarios.
- A direct native/interpreter marker probe records `events=6`, `begin=3`,
  `end=3`, `lane=1`, `phase=2` for host to GPU to host callback flow.
- Minimal native SSpec probes for `step()` and helper-function
  `expect(true).to_equal(true)` pass without unresolved stubs.

## Impact

This no longer blocks native SSpec coverage for the host-GPU lane marker
feature in the current checkout. It still does not prove real runtime queue
transport or GPU backend submission; those remain tracked separately by the
host-GPU runtime queue emission plan.

## Next Step

Add a tracked, canonical rebuild path for `src/runtime/libsimple_runtime.a` or
move native test linking to a generated archive from `src/runtime/runtime_native.c`
so fresh checkouts cannot accidentally use a stale untracked C runtime archive.
