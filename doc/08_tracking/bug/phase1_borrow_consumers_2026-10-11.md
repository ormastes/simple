# Six BorrowChecker consumer imports

The retained specs below fail to resolve BorrowChecker through a package glob
or package projection. Add the explicit class owner import alongside the
existing imports. Every original fixture, case body and assertion is unchanged.
Current release already exports the class from mod; no production facade repair
is included. This is the same test-only repair as PR3038, in additional consumers.

| Spec | Current complete cached diagnostic |
| --- | --- |
| compiler/borrow/iso_move_assign_field_spec.spl | 8/8 PASS |
| compiler/borrow/iso_move_return_spec.spl | 7/7 PASS |
| compiler/borrow/iso_move_sites_spec.spl | 2/2 PASS |
| compiler/mir/mir_transfer_operations_spec.spl | 5/5 PASS |
| compiler/resource/resource_drop_exactly_once_spec.spl | 6/6 PASS |
| compiler/resource/resource_use_after_move_spec.spl | 3/3 PASS |

All paths are under test/01_unit. Six distinct full spec files executed once,
31 cases passed, no reported case failures. The main borrow_check_spec's 13
current green criteria were excluded. No compiler rebuild or cache deletion.
All altered source bytes and terminal logs are hashed in the *-residual.json
receipts under build/phase1-borrow-owner-imports-20261011/; RESIDUAL_RESULTS.json
contains the wider group, including the failures and timeout excluded here.

Producer SHA256: 15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Qualification is BOOTSTRAP_DIAGNOSTIC_ONLY. Imported production closure and
native borrow semantics are not admitted; no global queue closure is claimed.

Excluded: iso_move_pipeline has three nil FunctionAttr fixture failures handled
in a separate interpreter lane; iso_parse_pipeline timed out once (no retry);
iso_use_after_move_e2e has two failures; resource_borrow_pinning has one real
unresolved assertion failure. Preserve all excluded assertions and diagnostics.
