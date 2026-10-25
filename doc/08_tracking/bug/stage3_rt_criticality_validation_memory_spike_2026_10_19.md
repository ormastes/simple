# Stage 3: rt_criticality HIR validation grows the compiler from ~5 GB to >42 GB

- Status: FIXED by 7cf083ccdc2 (PR #3876, two-pass streaming in validate_rt_criticality_diagnostics_blobs); Stage 3 confirmation pending
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Blocks: Stage 3 (bootstrap_main) after HIR lowering completes.

## Observation

Stage 3 resumed from r13 (r8 base 534a2b3e380 + 5bc133fb1c2 + #3833 +
810056927a2 validation-blob scope fix; admitted Stage 2 sha256
`e6cb4bfd5533a790de0d635687115b747e3b68b99e9ca9761153f58f73f7b210`), direct
route (one process), headroom/MemoryHigh 48G, MemoryMax 50G, watchdog cap
46 GiB:

| time | main RSS | phase |
|---|---|---|
| 19:12:46 | 3.3 GB | HIR 169/1315 |
| 19:22:47 | 5.0 GB | HIR 490 |
| 19:42:49 | 4.6 GB | HIR 1071 |
| 19:50:50 | 6.2 GB | HIR 1315/1315 done, validation |
| 19:51:50 | 15.6 GB | validation |
| 19:52:50 | 25.4 GB | validation |
| 19:53:51 | 34.7 GB | `phase3:hir:validate:rt_criticality:start` |
| 19:54:28 | stopped (unit peak 42.3G + 4.0G swap) | |

HIR lowering itself is now flat (~2-5 MB/module, versus ~57 MB/module before
810056927a2). The last phase marker is
`phase3:hir:validate:rt_criticality:start`
(`driver_hir_pipeline_support.spl:339`, which calls
`validate_rt_criticality_diagnostics_blobs`); the ~36 GB growth happens in the
validation passes after `layer_eq`/`effects`, ending inside rt_criticality.

The live headroom guard stopped the unit at `available_kib=47520544` (reserve
48 GiB). Host availability was also reduced by a concurrent Phase 4
diagnostic (`scratchpad/phase4/r13p4`: r13 Stage 2 native-build, ~6 GB main
plus 9 `run` workers at ~2 GB each), so the guard fired before MemoryMax.

## 2026-10-25 bounded duration observation

On frozen source `83be266ace41f453c69edf3c7f92521b5d573483`, the current
attempt completed HIR for 1,453 modules at `+3177585ms`. The log entered
`phase3:hir:validate:rt_criticality:start` at `+3190295ms`. The later bounded
process sample was at 58:59 elapsed, 57:57 CPU, and 13.91 GiB RSS; the RT gate
had no completion marker at that sample. This is a duration observation only:
no profiler or stack was collected, so it does not establish a hang, an
asymptotic complexity defect, or which inner function occupied the sample.

The current source proves the work envelope. `validate_rt_criticality_diagnostics_blobs`
walks every encoded HIR blob in its census pass. For each blob,
`rt_blob_declaration_census_unscoped_v1` decodes the HIR and compares a fresh
canonical re-encode with the input; the current call uses the default
`verify_canonical=true`. If the verified inventory contains RT claims or HAL
functions, it then walks the unique modules again to decode function facts.
With no claims and no HAL, it returns after the full census pass. These are
per-input linear passes with potentially expensive whole-HIR codecs; no
quadratic runtime claim is made.

The landed `7cf083ccdc2` change streams one decoded module at a time to bound
retained memory. The current blob route's no-claims early exit avoids the
second facts pass after the census, while still performing that census; its
`has_rt_hal_flags` and `claim_counts` parameters are not read in this path. The local
`709d74ec1bf` proposal adds canonical-entry provenance to skip re-encoding
verbatim HIR cache entries, but it is not in the current `release_phase3` or
frozen source. The current HIR log reports 121 cache hits and 1,332 misses, so
that proposal would cover only the hit subset for this attempt.

An opt-in `SIMPLE_ENUM_REG_TRACE=1` diagnostic addition is under source review.
It reports bounded counts and elapsed time for census, second-pass fact
extraction, and graph boundaries without printing source payloads. No runtime
qualification or speedup claim is attached to that instrumentation.
