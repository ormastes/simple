# Retained producer HIR progress reports success alongside fatal errors

Status: observed in immutable retained producer; current-source regression qualification pending. Bug DB reconciliation pending.

Producer SHA256: a6b18fd84c5f88a48afa0beaf61434f39678155fb0f0ed01127db25a28cf5078.
Evidence: build/native_probe/pure-loader-api-20261011-astra/attempt2/RESULT.json
RESULT SHA256: 45902a588dcd514a3c3722ae50ede18681e35c4f3cbd408f9d738b913a8f6e3c.

Both actual ordinary native-build invocations finished source loading (120/120) and reached HIR. Progress reported succeeded=120 failed=0 despite hir-fatal/hir-poisoned rows and terminal error totals 740/733. Both native exits were 1; no fixture executable was produced and runtime tests were not dispatched. The totals count errors, not failed modules. Diagnostic display caps prevent deriving a complete module/name census from the displayed summary alone.

This is an observation about the frozen producer, not a claim that current shared source still has the same defect. Current driver_hir_pipeline_lowering.spl contains poisoned-module rejection and progress paths; comparison and a real producer-bound regression are required before changing them.

Required regression coverage:
- One valid and one fatal HIR module: attempted=2, succeeded=1, failed=1, terminal aggregate failure, only valid module eligible for object generation.
- Recoverable warnings leave a module successful; multiple fatal diagnostics count one failed module while preserving the exact diagnostic count.
- A poisoned module followed by a valid module must continue without contaminating the latter's counters or object eligibility.
- Cached successful modules have explicit cached status; blocked/unrun modules must not be counted successful.
- Memory snapshot or receipt publication failure must preserve nonzero terminal status and not publish a success record.

Tests: UNRUN. No shared source fix applied. Do not rewrite historical receipts or use the misleading progress line to admit Phase3.