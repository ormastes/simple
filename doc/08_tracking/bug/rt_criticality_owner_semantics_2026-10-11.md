# RT criticality owner semantics (2026-10-11)

Status: focused bootstrap diagnostics PASS; production admission OPEN.

## Selected requirements and current-source defects

The five retained failures in `rt_criticality_spec.spl` establish the selected
scope. Its original bodies and assertions remain unchanged; draft PR 3019 owns
the independent retired-import repair. The immutable release owners lacked the
rank, scalar assurance closure, and typed-validator APIs required by those tests.

| Requirement | Required behavior | Existing failed case / new regression |
|---|---|---|
| REQ-RT-OWNER-001 | Verified is stricter than critical and requires no lower-tier reason | admits verified as stricter than critical without a lower-tier reason |
| REQ-RT-OWNER-002 | Implicit/critical rank 3 and verified rank 4 are independent of global profile | treats verified and unqualified roots as fatal assurance independently of the global profile |
| REQ-RT-OWNER-003 | A lower caller inherits a reachable critical dependency's scalar rank | promotes a lower root to a reachable critical dependency with scalar closure state |
| REQ-RT-OWNER-004 | Explicit lower allocation is a typed warning in the configured migration epoch | keeps an explicitly lower allocation in the configured warning migration phase |
| REQ-RT-OWNER-005 | Exact reviewed allocation authority survives validator admission | preserves exact reviewed allocation authority through the shared validator scratch |
| REQ-RT-OWNER-006 | The actual driver rejects verified allocation even when a reason is supplied | new driver routing regression |
| REQ-RT-OWNER-007 | The actual driver emits lower-tier warnings without fatal promotion | new driver routing regression and captured diagnostic output |
| REQ-RT-OWNER-008 | Different ambiguous declaration identities retain separate diagnostics | new ambiguous claim regression |

The prior `rt_critical_profile` excluded verified, and a supplied reason let its
declaration avoid critical effect admission. Ordinary roots also received a
HAL-only synthetic edge before digest verification, invalidating their exact
reviewed manifest authority. The actual post-HIR driver omitted RT validation
entirely, so restoring only an API would leave these policies unenforced.

## Repair and interfaces

`rt_criticality.spl` owns the fixed assurance lattice, diagnostic severity/value
types, and scalar reverse-edge worklist. Only a larger reachable rank propagates;
each rank rises at most four times, bounding this closure to O(V + E). Existing
effect closure, digest material, manifest checks, and sorting code are retained.

`rt_criticality_validation.spl` resolves claims once, computes effective ranks
once, and returns typed diagnostics. Ordinary roots retain their original fact
graph for exact manifest digest verification. HAL roots retain the existing
compiler-reviewed intrinsic route. Lower-tier allocations follow the configured
migration epoch. Empty and ambiguous roots deduplicate by their individual claim
keys. The existing `validate_rt_criticality` signature remains an error-only
string adapter; the typed adapter clears reviewed authority once per validation.

`driver_hir_pipeline_support.spl` invokes the typed adapter in its existing
post-HIR validation route, reached by three lowering callsites. Its helper emits
warnings through the existing diagnostic sink and returns errors to the fatal
driver result. Warnings are not silently dropped by the compatibility adapter.
Current HIR extraction, optional range handling, FloatLexeme, ConvertCall,
layout validation, and aspect validation remain intact. No historical owner file
was replaced wholesale and no test helper substitutes for production semantics.

## Bounded evidence

Evidence: `build/phase1-rt-criticality-repair-20261011/` in the owning workspace.
`SOURCE_BINDING.json` records the immutable base and actual owner source hashes
inlined into baseline/repaired artifacts. `SOURCE_BINDING_DRIVER.json` records
the final owners and actual driver helper inlined for the three new cases.
Supporting HIR/stdlib imports and the producer remain unadmitted.

Cached Stage 1 producer SHA256:
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
Bounded collector SHA256:
`6e7d07e3f42ae203f6ad8086122f3aecf4e90ed3b093c7af45017e1461601cdc`.
All launches used 60-second timeout, 1 GiB job RSS, 1 MiB log, 3 GiB disk floor,
64 MiB artifact growth, and terminate-job cleanup.

| Cycle | Executed | Passed | Failed | Peak job RSS (KiB) |
|---|---:|---:|---:|---:|
| Current owner baseline, only five retained failures | 5 | 0 | 5 | 102216 |
| Repaired owners, same five unchanged case bodies | 5 | 5 | 0 | 102480 |
| Final driver severity/dedup changes, only three new cases | 3 | 3 | 0 | 106268 |

The final log contains the real emitted warning:
`[post-hir-validation-warning] warning[RT-W-STEADY-ALLOCATION-001]: explicit lower-tier RT closure 'malloc_driver_warning' contains unproved steady-state allocation`.
All receipts report zero final active job members. No compiler was rebuilt.
The five repaired greens and the 21 previously passing cases were not replayed.
Three cause cycles are consumed; no fourth cycle is permitted for this feature.

## Outstanding admission

These are actual current-owner source diagnostics, not admitted pure-runtime
qualification. The original spec's real import closure, the new regression's
driver import closure, native value behavior, and the full driver pipeline still
need admitted execution. Required compiler/lib/MCP/LSP checks and core/MCP smoke
gates remain unavailable. The production PR stays draft; retained backlog rows
remain OPEN/NOT_PROVEN. No tag, publication, or release PASS is claimed.
