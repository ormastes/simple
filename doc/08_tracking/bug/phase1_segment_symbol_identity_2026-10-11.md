# Phase 1 segment symbol identity and owner sealing (2026-10-11)

Status: source repair; cached bootstrap diagnostic PASS; admitted pure-Simple
compiler/core/MCP verification pending. Keep the integration PR draft until
those gates pass. No release qualification or publication follows.

Current release `c4cd4530c1d4e61d74ce669d54b9e26c0d625a44` reproduces the retained
loader case: 10 executed, 5 passed, 5 failed. Three scenarios cannot seal their
owner, one cannot validate stale symbol snapshots, and one overwrites a live
symbol owned by another module. These are current production defects, not
missing files in the retained source projection.

REQ-SEGMENT-IDENTITY-001: symbol binding must refuse cross-owner/name collisions
and retain the original binding; identical rebinding is idempotent.
REQ-SEGMENT-IDENTITY-002: snapshots carry the mapping generation and mapper
instance, and fail freshness checks after release/reuse or in another mapper.
REQ-SEGMENT-IDENTITY-003: owner sealing uses the existing native protection
owner, seals each writable segment once, and refuses unknown owners.
REQ-SEGMENT-IDENTITY-004: binding extents fail closed even when offset plus size
would overflow signed i64.

The existing segment resolution spec covers symbol offsets, distinct addresses,
real machine-code calls returning 11/22/33, owner release, stale snapshots and
name conflicts. Added controls cover exact-rebind idempotence, changed extents,
max-i64 overflow, cross-mapper identity and actual execution after writable
owner sealing. Defaulted snapshot fields preserve existing constructor callers.
The extent guard uses subtraction after checking the offset, so no unchecked
addition can fabricate an in-bounds symbol.

Evidence: `build/phase1-segment-symbol-owner-20261011/baseline-result.json`,
`final-result.json`, and `fixed-result.json`. Final segment spec: 14 executed,
14 passed, exit 0 (1.43 seconds). Unchanged clear teardown spec: 5 executed,
5 passed, exit 0 (1.61 seconds), run once. The Stage 1 cached producer SHA256 is
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
No compiler rebuild or passing-check replay occurred. Source/test hashes are
retained in the result artifacts.

BUG-PHASE1-OPTION-ASSERT-20261011: the cached producer's generic `assert_eq`
helper compares typed `Option::None` against raw `nil` and rejects absence.
The first repaired diagnostic exposed this as the remaining 1/14 failure.
The spec now asserts the same `lookup(...) == nil` predicate in its typed
expression, matching existing loader teardown specs; absence is still required.
The optional assertion helper/runtime defect remains open for its owner.

Pending admission: qualified pure-Simple compiler/lib/MCP/LSP checks,
MCP interpreter integration, core runtime smoke and MCP native smoke. The
corrected cached pure-Simple composition has only LLVM hello diagnostic evidence
(`CAPTURED_CORRECTED_COMPOSITION_NOT_QUALIFIED`; six products unqualified), so
it was not used to assert these gates or restart another owner's controller.
