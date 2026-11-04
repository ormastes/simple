# Caret closure: enum payload, local binding, collection method HIR/MIR failures

Status: OPEN (split from caret_essential_leaf_provider_gaps_2026_10_10, 2026-11-03).

The parent bug covered missing leaf providers (file_read, print_raw, pane-manager
adapters) and leaf type gaps (ModelProfileV1 import, SMTP `List` return types).
Those are repaired and verified: test/01_unit/app/llm_caret/essential_leaf_provider_spec.spl 3/3 and
test/01_unit/lib/smtp/recipient_array_type_spec.spl 3/3.

The remaining Caret closure failures are three separate compiler classes, not
missing providers:

1. enum payload lowering diagnostics
2. local binding (pattern/val) diagnostics
3. collection method owner diagnostics (e.g. `then`, `is_open`, `close`, `trim`
   owners reported by the CS fixture MIR failure)

Enumerating the exact modules/lines needs a fresh Caret closure HIR run on a
stage3 producer (323-module closure, ~240 s, 62 diagnostics in 14 files at the
last run; evidence: /home/ormastes/simple-phase4-web-a0-parallel-20261010/caret/build/failure-summary.json).

Repro: build the Caret essential closure with the stage3 producer and collect
`failure-summary.json`; triage each diagnostic into the three classes above and
file per-instance rows. No suppression of diagnostics.

## 2026-11-04 triage note (cross-ref native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19)

TEST_BLOCKED: no per-instance split is possible without a fresh Caret closure
HIR/MIR run on a stage3 producer; the seed native-build path fails SCV
admission in sparse worktrees and the 2026-10-10 failure-summary.json is not
on this host. Source facts established today (release/1.0.0 80f074e5782):
- `src/lib/nogc_async_mut/io/buffer.spl` has no lambda literals at all, so the
  `E-MIR-EXPR-Lambda x21` sites cited for it in the 2026-10-19 bug no longer
  exist in that file; lambda lifting for non-Let positions is implemented
  (`expr_dispatch.spl` `case Lambda`, `lower_lambda_value`).
- `close`/`is_open` in that file are now explicit forwards
  (`buffer.spl:290-297`) from the stage2 workaround commits (290304c37e0,
  515f96e824e), not unresolved methods.
Next step: run the Caret closure HIR/MIR on stage3, one row per diagnostic.
