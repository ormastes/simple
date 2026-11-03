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
