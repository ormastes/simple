# Native SSpec host-GPU lane process SFFI crash

## Status

Source-fixed; strict execution proof pending. The original `step()` path was
fixed, but a 2026-07-18 prevention audit found that an expect-only top-level
helper was rewritten from `expect(...)` to `expect ...` after helper detection
had been limited to the parenthesized spelling. Hosted weak-stub fallback could
therefore false-green that case.

Both the pure-Simple runner and bootstrap-seed runner now recognize the
rewritten spelling and inject the real `rt_bdd_expect_truthy` helper. Stub-dump
output is refreshed even when no unresolved symbols remain. The focused
`scripts/check/check-native-sspec-expect-helper.shs` gate uses strict no-stub
mode and requires the deliberately false helper assertion to report one
failure with an empty stub dump.

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

Run `sh scripts/check/check-native-sspec-expect-helper.shs` with the rebuilt
pure-Simple compiler. Then record per-platform execution separately; the
historical evidence above is Linux x86_64 only.
