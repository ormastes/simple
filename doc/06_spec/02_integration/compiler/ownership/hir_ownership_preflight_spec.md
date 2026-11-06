# Actual CLI ownership preflight

Status: authored manual; NOT_EXECUTED and docgen pending an admitted full runtime.

Source: `test/02_integration/compiler/ownership/hir_ownership_preflight_spec.spl`.

1. Parse genuine @no_gc(strict) sources and admit typed parameter-effect contracts.
2. Reject read-after-move and repeated loop transfers; accept exclusive arms and dominating refill.
3. Validate the complete retained closure before entry effects. The CLI negative must report moved use and omit OWNERSHIP-ENTRY-MUST-NOT-RUN.
4. Execute the valid exclusive-path control through the same exact CLI.
5. Treat missing runtime, missing contracts and exhausted budgets as failures, never PASS.

No full ownership/drop/runtime/backend qualification is claimed.
