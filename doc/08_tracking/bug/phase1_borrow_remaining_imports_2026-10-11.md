# Open BorrowChecker consumer diagnostics

Status: draft import repairs; actual residual failures and timeout remain open.
No assertion is weakened and no producer/native admission is claimed.

Three further specs now import BorrowChecker from its defining mod module:

| Spec under test/01_unit | Current diagnostic |
| --- | --- |
| compiler/borrow/iso_use_after_move_e2e_spec.spl | 4 executed, 2 passed, 2 failed |
| compiler/resource/resource_borrow_pinning_spec.spl | 1 executed, 0 passed, 1 failed |
| compiler/borrow/iso_parse_pipeline_spec.spl | One 40-second timeout; no terminal case verdict |

The two end-to-end failures are moved-then-reused ISO local and moved ISO local
used as a call argument (`print x`). The pinning failure expects a diagnostic
for a Ref followed by Drop of the same resource. Its existing spec describes
the absent lifetime/foreign-call pinning infrastructure; do not replace the
assertion with a fabricated diagnostic or reject unrelated valid drops.

Concrete performance issue: the parse-to-borrow-check integration did not finish
within the bounded 40-second source launch after its explicit owner import.
This is a timeout, not a measured compiler regression or a passed/failed case
count. Preserve the partial log; investigate parsing/lowering owners or an
admitted producer before another supported cause cycle. No blind retry.

Receipts/logs: build/phase1-borrow-owner-imports-20261011/*-residual.json and
*-residual.log; full wider outcomes in RESIDUAL_RESULTS.json. Exact source and
terminal/partial log bytes are hashed. Producer SHA256:
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Qualification: BOOTSTRAP_DIAGNOSTIC_ONLY; current imported owners unadmitted.

This draft changes only imports and this tracking note. The six fully passing
consumers and the main borrow spec land separately; ISO pipeline FunctionAttr
fixtures are handled in their own reviewed branch. No rebuild/cache deletion.
