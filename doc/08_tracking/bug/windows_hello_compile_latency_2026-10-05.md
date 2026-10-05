# Windows Hello compilation latency

Status: OPEN. Measured diagnostic evidence; root cause and fix unverified.

## Target and scope

The requested target is less than 0.1 seconds to compile the Hello use case.
Report end-to-end compilation separately from compiler phase timings and program
execution. Identify cold source admission, warm source snapshot, and warm artifact
cache conditions explicitly. A cached output lookup alone does not establish the
compilation target. Do not stop or restart the active bootstrap to apply this fix:
continue its current source generation through Phase 4 and preserve its caches.

## Reproduction evidence

Pure-Simple Phase 2 producer source: `916be6c20617637e2cccf3d18c23669470ab8ffe`.
Producer SHA256: `2b83155910336e56ec8b663c3d3e7d3ceb9c61b60fa98182163f9670ff044c33`.
Input: `test/04_smoke/windows_native_hello.spl`, 65 bytes, one compiled module.
The source snapshot contains 16,357 files.

Evidence directory on the Windows host:
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004`.
Each packet below contains `results.json` and its dedicated
`verified-hello.json`; compilation and execution both returned zero and produced
the expected output. These monitor-only diagnostic runs are not RC admission.

| Packet | Compile seconds | Run seconds | Peak process-tree RSS KiB |
| --- | ---: | ---: | ---: |
| `qualification-916be-hello-cranelift1` | 361.635 | 0.782 | 3376680 |
| `qualification-916be-hello-llvm1` | 141.597 | 0.829 | 3959476 |

Cranelift started with no source snapshot. LLVM reused that snapshot, but both
runs reported frontend 0 hits / 1 miss / 1 parse and HIR 0 hits / 1 miss / 1 store.
Neither is evidence of a fully warm artifact-cache build. Different backends
also prevent treating their time difference as a measured cache speedup.

Driver-reported source-loading-through-HIR durations total approximately 418 ms
and 470 ms respectively. File timestamps bound the following intervals; they
are not instrumented phase durations and do not establish exclusive CPU costs:

| Interval | Cranelift seconds | LLVM seconds |
| --- | ---: | ---: |
| Invocation to snapshot publication | 295.085 | Existing snapshot |
| Invocation to frontend artifact | 307.689 | 70.352 |
| Object to executable | 41.509 | 49.534 |

## Investigation and regression requirements

1. Instrument admission, snapshot validation/materialization, closure publication,
   provider setup, runtime object reuse, and linking with monotonic elapsed time
   and phase-associated memory observations. Preserve source and provider identity
   checks; repeated scans are a hypothesis, not yet a demonstrated cause.
2. Measure the same backend with cold and warm conditions and report actual cache
   hit/miss counts. Compare equivalent source, toolchain, runtime, flags, and output.
3. Exercise representative small and larger programs, imports, arrays and tuples,
   both backends, and execution of the produced binaries. Assert real outputs.
4. Cover source/dependency changes, changed backend/runtime/configuration, missing
   and malformed cache artifacts, failed compilation, and interrupted publication.
   No optimization may turn stale, incomplete, or mismatched data into a cache hit.
5. For each performance change, check memory retention across repeated work and
   peak RSS as well as result correctness. For memory changes, check time and
   correctness. Record regressions and unresolved failures independently.
6. Keep the active bootstrap immutable. Integrate reviewed fixes into a subsequent
   source generation, with exact producer/source identities and cache invalidation.

The latency defect is established. Its allocation owner, dominant exclusive
phase costs, algorithmic cause, and attainment of the target remain unverified.
