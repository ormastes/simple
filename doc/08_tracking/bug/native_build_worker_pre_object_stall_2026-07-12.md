# Native-Build Worker Pre-Object Stall

## Status

Partially fixed. The pre-object stall no longer reproduces after the
entry-closure queue and line-scan fixes: the 2026-07-12 full bootstrap emitted
617 cached objects and a 126,818,048-byte Stage 2 binary. Deployment remains
blocked later in the pipeline.

## Reproduction

```sh
bin/simple native-build --backend cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 8 \
  --cache-dir build/native_probe/field-map-worker-cache --mode dynload \
  --entry src/app/cli/native_build_worker.spl \
  -o build/native_probe/simple-field-map-worker
```

The split native-build module must import `compiler.driver` rather than the
ambiguous `compiler.driver.driver`; otherwise semantic analysis fails with
`compiler_driver_create not found`.

After that import is corrected, the build remains CPU-bound for more than eight
minutes after warnings, emits no further phase diagnostic, and creates no object
files. It was terminated rather than retried indefinitely.

## Current Blockers

- Stage 3 runs the Stage 2 binary at one core for several minutes and exits 139.
- Stage 4 reaches native-project discovery but rejects
  `src/lib/common/encoding/sfnt.spl` at EOF with `expected expression, found
  Dedent`, despite `simple check` accepting the file. This parser blocker is
  now fixed by normalizing both trailing-operator continuations in the final
  function; the parser regression checks every complete top-level prefix.
- The Stage 2 artifact is not a usable CLI: `-c 'print(1+1)'` remains CPU-bound.
- After the parser fix, Stage 4 compiles 1,042 objects and reaches the linker.
  It then fails because the full CLI closure references hosted-only symbols
  (`rt_process_run_timeout`, `spl_dlsym`, `spl_wffi_call_i64`, GUI adapters,
  and others) absent from `core-c-bootstrap`. Hosted/native-all bundles are
  intentionally rejected by current native-build policy, and no ABI-complete
  host `simple-core` archive is available.

## Remaining Fix

Preserve the 1,042-object cache, isolate the Stage 3 crash, and provide an
ABI-complete pure `simple-core` host runtime for the full CLI closure (or remove
hosted-only dependencies from that closure without weakening CLI behavior). A
successful fix must produce a Stage 4 CLI that passes `-c 'print(1+1)'` and the
deployment smoke gate.

## Simple-Core Host Progress

The first dedicated `simple-core-host` archive now force-links the existing
runtime, compiler SFFI, hosted platform owners, and production C runtime/SQLite/
SDL/SIMD sources without exposing the Rust `rt_native_build` handler. Stage 4
unresolved symbols dropped from 237 to 78 after removing accidental LLVM/C++
objects and adding the C owners.

The remaining set is recorded in
`build/native_probe/simple-core-c-missing.txt`. It contains three actionable
groups: memtrack and SDL transitive link ownership, optional GPU backend ABI
(ROCm/oneAPI/OpenCL/OpenGL), and Simple-to-Simple closure misses such as
`run_check`, `json_serialize`, and iterator trait methods.
