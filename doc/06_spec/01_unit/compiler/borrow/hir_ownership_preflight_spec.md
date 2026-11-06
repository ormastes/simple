# Typed HIR ownership flow

Status: authored manual; NOT_EXECUTED and docgen pending an admitted full runtime.

Source: `test/01_unit/compiler/borrow/hir_ownership_preflight_spec.spl`.

1. Parse genuine @no_gc(strict) sources and admit typed parameter-effect contracts.
2. Reject read-after-move and repeated loop transfers; accept exclusive arms and dominating refill.
3. Validate the complete retained closure before entry effects. The CLI negative must report moved use and omit OWNERSHIP-ENTRY-MUST-NOT-RUN.
4. Execute the valid exclusive-path control through the same exact CLI.
5. Treat missing runtime, missing contracts and exhausted budgets as failures, never PASS.
6. Reject non-place derived short borrows and ownership-sensitive globals while retaining scalar globals.
7. Admit aliased imported short-read/mutate calls through live physical source authority; reject missing, wrong-path and changed-effect generations. Direct backend calls lacking provider context fail closed.

No full ownership/drop/runtime/backend qualification is claimed.

Additional authored controls bind resolver provenance and physical aliases, reject owning projections through copyable global handles, and reject direct-entry consume-to-short row forgery through canonical reinference. These remain NOT_EXECUTED.
