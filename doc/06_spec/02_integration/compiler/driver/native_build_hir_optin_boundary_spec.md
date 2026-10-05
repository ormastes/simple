# Explicit HIR-only admission boundary

Executable: `test/02_integration/compiler/driver/native_build_hir_optin_boundary_spec.spl`.
Status: authored, native execution **UNRUN**. This manual records expected
checks, not measured results.

| Scenario | Real boundary and required evidence |
|---|---|
| Valid authority, parse off, HIR on | Create a two-module Git fixture; acquire/publish its canonical snapshot; invoke candidate native-build with 20 jobs; require 20 completed workers, exactly 20 distinct owner `.done` records with exact hash filenames and contents, zero failed workers/modules and zero unfinished modules; execute the resulting binary successfully. |
| Missing source inventory digest | Invoke the candidate with the published snapshot but an empty source digest; require nonzero exit, `SCV-E-HIR-ADMISSION`, no HIR queue, and no output artifact. |
| Missing inventory generation | Same rejection checks with only the generation removed; serial success is forbidden. |
| Unavailable inherited snapshot | Call the real coordinator in-process; require exit 1, no queue/artifact, unchanged eight authority fields, and restored worker/warm-candidate markers before test cleanup. |
| Similar suppression settings | Call the production shard-count function: valid opt-in yields 20; HIR-cache off, frontend-cache off, HIR child, parse child, and explicit HIR disable each yield zero. |

The invalid cases inspect the private HIR directory as well as diagnostics.
The coordinator creates its HIR queue before spawning HIR children, so absence
of that queue is the rejection oracle. These tests do not count unrelated Git
or metadata subprocesses as HIR children. A completed pool of 20 workers proves
worker execution, not 20 simultaneously CPU-active workers or a speedup.

The fixture requires the actual candidate path in `SIMPLE_HIR_BOUNDARY_CANDIDATE`
and its digest in `SIMPLE_HIR_BOUNDARY_CANDIDATE_SHA256`, and verifies its bytes.
It uses the canonical authority APIs, real Git/filesystem state,
and normal subprocess execution. It does not substitute worker results or
mock admission. Environment changes are restored after each call; the
in-process rejection case samples production restoration before test cleanup.

Run under the shared 80-job scheduler with one 20-job reservation. The test
runner must serialize these environment-mutating cases. Preserve source,
producer, queue, cache, output, and process receipts. RSS/performance,
simultaneous claims, crash recovery, and cross-owner cache corruption have
separate coverage and must not be inferred from these assertions.
