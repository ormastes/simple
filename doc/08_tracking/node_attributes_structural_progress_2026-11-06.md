# Node attributes: lifecycle integration progress

Target branch: `release/1.0.0`. Date: 2026-11-06.
Architecture/design landed in #7228. Status: implementation in progress;
execution qualification pending. This is not full node-attribute completion.

## Canonical ownership and review resolution

PR #7241 was rebased onto release commit `d3b2459be58` after the owner review
identified the schema resolver already landed in #7220. There is one resolver:
`compiler.common.data.data_schema_resolver.data_schema_resolve_v1`, producing
`DataSchemaSurfaceV1` with `data_schema_digest_v1`.

The duplicate NodeAttribute schema contracts, resolver, ordering, dependency
validation and semantic encoding were removed from this change. The experimental
compiler contexts, property bindings and annotation adapter that depended on
those types were also removed. Their authored test counts are not qualification
of the canonical implementation and are no longer reported as current coverage.
Source/SDN, visibility/effects, computed properties, independent contexts and
explicit off-mode behavior remain full-feature requirements. Extend the canonical
owners for these features rather than restoring a parallel schema stack.

`src/compiler/00.common/data/node_lifecycle_contracts.spl` retains whole-node
Pending/Ready/Discarded facts, the initialization bitmap, retaining finish failure,
duplicate-init checks, explicit discard recording and unresolved-scope diagnostics.
It now consumes `DataSchemaSurfaceV1`, validates its digest and canonical one-based
attribute IDs, and binds facts to that digest. It moved out of library/common
because importing the compiler-owned schema there would invert the dependency.

The canonical V1 schema describes stored fields and infers views from fields.
The lifecycle adapter therefore refuses an unknown/fieldless view rather than
inventing a view declaration. Computed/forwarded readiness and explicit empty
views require extension of that owner before admission. All applicable stored
slots, including optional absence/default values, require actual initializer
commits. No implicit zero or inferred executed default is introduced.

These are semantic facts, not user-owned payloads or mintable runtime authority.
They do not allocate, clean up, publish or retire nodes, execute defaults, enforce
language must-resolve rules, or replace topology/borrow checks. Digest checking
is on this cold fact path, not on ready-node reads.

## Evidence

`test/01_unit/compiler/data/node_lifecycle_contracts_spec.spl` authors eleven cases
against the canonical resolver: retaining failure, default bookkeeping, duplicate
initialization, discard, digest mismatch, canonical ID bounds, stale surfaces and
unsupported versions, refusal of an unrepresented empty view, cross-view
applicability, explicit optional-absence commits and malformed IDs/bitmaps. These have
not executed; no passing count or coverage percentage is claimed.

The separate canonical Windows LLVM bootstrap remains pinned to release commit
`6e03930143983a5c9861321f67aff300b07f16ed`. It uses
`bootstrap-windows.sh --msvc --strategy=normal --full-bootstrap --stop-after-stage2
--backend=llvm --jobs=1`. Attempt 4 passed materialization verification and native
C admission. Seed and native-all compilation then completed with native exit 0,
but the parent aborted on a lost shared-lock claim before self-hosted admission.
A focused cross-runtime probe reproduced a live MSYS owner being classified dead
from Git Bash; see [the lock bug](bug/portable_lock_cross_msys_namespace_false_dead_2026-11-06.md).
Attempt 5 uses the same Git Bash runtime as the other active bootstrap while
preserving compiled objects and ownership/receipt checks. It passed receipt,
native C admission and fingerprint/toolchain checks, then stopped at the shared
cache ownership wait while the foreign owner (native PID 27876) remained live.
Its bootstrap log records `ABORTED: stage=fingerprint exit=1`; the outer
PowerShell wrapper returned 0 after restoring PATH, which is not build success.
Do not retry the unchanged occupied-lock condition or remove the foreign claim.
The cached successful Cargo outputs remain intact. This document does not
prove current process liveness or successful bootstrap. Logs remain in the frozen worktree at
`build/node-attributes-qualification/bootstrap-attempt4.log` and `bootstrap-attempt5.log`.

Earlier attempts established environment failures: MSYS Python was incompatible
with the native supervisor; a restricted PATH lacked PowerShell; Git-for-Windows
failed receipt validation before compilation. No receipt gate was bypassed.
Installed Rust seed executables were not used for feature tests. #7220's reported
seed test evidence is not pure-Simple qualification of this lifecycle adapter.

## Remaining landing and feature gates

Resume evidence (2026-11-07): the foreign bootstrap terminated at Stage 2 with
a 300-second `driver_aot_pipeline.spl` worker timeout and released its claim.
It produced no admitted test runner. PR #7241 was rebased onto release commit
`3c63201ea63`; its canonical data-schema owner is unchanged. Attempt 6, the final
attempt under the six-cycle limit, reuses the frozen source and cached Cargo
outputs with Git Bash. Its outer wrapper now propagates the actual bootstrap
exit status after restoring PATH. No further unchanged retry is authorized by
the bounded-repair policy; inspect its actual terminal evidence first.

Attempt 6 terminal result: **ABORTED, stage=stage2, exit=1**. The frontend sanity
substep refused to build with 9,121 MiB RAM/commit headroom against the configured
24,576 MiB `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` reserve (substep exit 2). The
diagnostic is in `stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-failure.log`
under the frozen bootstrap output. No Stage 2/full-CLI/test-runner admission or
lifecycle test execution resulted. The diagnostic check's PASS only means the
failure had an explanation; it is not bootstrap success. Six bootstrap attempts
are exhausted. Preserve artifacts and do not start a seventh attempt or lower
the reserve implicitly. Further execution needs an admitted runtime supplied by
another lane, or an explicit retry-policy change with adequate resource headroom.

Execute the lifecycle spec with an admitted pure-Simple runtime, assess failure
coverage, and complete applicable compiler/lib/MCP checks before marking this
change qualified. Review the exact pushed diff and comments before landing.
The broader requirement matrix remains in `doc/03_plan/sys_test/node_attributes.md`:
source/SDN declaration binding, generated places, real builders and cleanup,
lifetimes/topology, storage layouts, engine parity, AOP, tracing, cache/LSP and
Simple/BuildRunner adoption remain required. W2c should build on this lifecycle
contract and the canonical resolver, not a new resolver.

## Explicit continuation and MIR/codegen scope (2026-11-07)

The user authorized another twelve hours of work and requested all MIR/codegen
bugs be addressed. This extends the exhausted bootstrap retry budget; it does
not waive execution or admission requirements. Attempt 7 uses the same frozen
source, compatible caches, one worker and the existing enforced process-tree
RSS limit, with an explicit 4 GiB free-memory reserve instead of the default
24 GiB. Initial available physical memory was approximately 5.7 GiB. The
attempt-6 rejected binary and sanity receipts were copied to
`build/node-attributes-qualification/attempt6-preserved` before continuation.
The new log is `build/node-attributes-qualification/bootstrap-attempt7.log`.
At this update the attempt is running; no admission or test pass is claimed.

MIR triage separates existing source repairs from unresolved native failures.
The nested-array push AV already has source repair `83c17508b4a`; its native
fixture now checks sibling-row integrity and remains unexecuted. Result Err
binding has an additional standalone generic-method fixture exercising actual
success/error payload values without the typed-alias workaround. Native trait
field assignment and dispatch are being investigated in their existing owners.
The peer build's 555 reported failures comprise one worker timeout and 554
unattempted operations, not 555 independently demonstrated MIR defects.

Subsequent bootstrap status: attempts 7 and 8 terminated unadmitted on inner
worker-policy and free-memory reserve gates respectively. Attempt 9 timed out
on output ownership while attempt 8 completed cleanup; it did not compile.
After both wrappers exited, attempt 10 started with the supported two-pass
route (`SIMPLE_FILE_WORKERS=0`) and a positive 2 GiB reserve, retaining the RSS
guard and normal admission checks. This is the final planned automatic reserve
adjustment. See [the MIR campaign](mir_codegen_repair_campaign_2026-11-07.md)
for retained measurements, added source candidates and unresolved failures.

The preflight timeout-forwarding fix has since landed through PR #7377.
Attempt 11, pinned to `08944a34d899a5beea2940b6a9688d08252e51bb`, passed
preflight and entered Stage 2 compilation with fresh materialization receipts.
The feature branch has been reconciled with release commit
`fe91477a710ada22f40249fb99b2c92ced7c92bd`, preserving newer implementations
and avoiding duplicate trait/diagnostic owners. Compiler tests and HIR
codec/hash regeneration still require the admitted self-hosted runner.
