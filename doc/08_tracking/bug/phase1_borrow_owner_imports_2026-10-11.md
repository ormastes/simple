# Phase 1 BorrowChecker owner import repair

The retained borrow_check_spec.spl reported six passes and seven failures, all
seven failing to construct BorrowChecker. Import its defining module explicitly:
compiler.borrow.borrow_check.mod. Keep the package import for graph helpers and
leave every executable body, assertion and fixture unchanged.

Current release e61f9d7976378060b6cc1762ee7034f5ffa653ec already exports the class
from mod in the package facade. No production facade repair is required here.
The cached diagnostic producer fails the facade-only binding but succeeds with
the explicit owner. The uncommitted main-workspace facade differs; it was neither
edited nor included in this repair.

Evidence: build/phase1-borrow-owner-imports-20261011. One unchanged original
failure body first failed with unknown class BorrowChecker, then passed after
the import. Six other original failed bodies passed once. Six graph criteria
that had not run in this repair session passed once in a separate fixture.
Incremental total: all 13 original case identities passed; the final full file
was not replayed. No current green criterion was repeated. All extracted bodies
and shared helpers preserve the original bytes apart from the added import.

Producer SHA256: 15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Qualification: BOOTSTRAP_DIAGNOSTIC_ONLY. This test import repair does not admit
imported production owners, qualify a native borrow checker, or close the global
historical queue. Receipt files baseline.json, repaired.json, remaining.json and
graph.json pin the exact entry and terminal log hashes. Their cases arrays
identify every grouped criterion. Separate *-cases.json files also record the
remaining-failure and graph criterion lists.

The wider retained group has 13 specs. Ten other direct consumer imports require
their own case qualification; two driver specs fail inside imported production
driver code and are outside this test-only repair. Preserve those open rows.
No compiler rebuild, cache deletion, raw runtime declaration or assertion
weakening occurred.
