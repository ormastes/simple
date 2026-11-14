# `is_read_only_handle_name` is private but imported by two other HIR modules

Bug ID: `hir_private_is_read_only_handle_name_imported_cross_module_2026-11-14`
Severity: P1 (every seed spec that loads HIR lowering fails at load). Status: fixed (`pub fn`, this change).
Layer: `20.hir`.

## Symptom

On `origin/release/1.0.0` at `4cc13ad1240`, with the seed
`simple-covexpr-20261114/build/seed-base/simple` (built from `6a71372cabc`):

```
semantic: private fn `is_read_only_handle_name` of module
`.../src/compiler/20.hir/hir_lowering/types.spl` is not visible to
`.../src/compiler/20.hir/hir_lowering/...`
```

`test/01_unit/compiler/20.hir/nil_unit_type_spec.spl` (untouched): 4 of 6.
`test/01_unit/compiler/mir/enum_payload_local_evidence_spec.spl`: 17 of 42 (42 of 42 at
`a91ccdb5f38`). `test/01_unit/compiler/mir/contextual_enum_payload_spec.spl`: 24 of 25.

## Cause

`f6e729f9a0b` (feat(hir): RevisionImmutable/FrozenImmutable handles, IMM-03/04) declares
`fn is_read_only_handle_name` without `pub` in `hir_lowering/types.spl:45` and imports it
from `hir_lowering/statements.spl:15` and
`hir_lowering/_Items/class_declaration_lowering.spl:6`. That commit touches no
`src/compiler_rust` file, so this is the pure-Simple source breaking the visibility rule, not
seed staleness; a Stage 2 built from this tip should meet the same rule.

## Fix

Mark it `pub fn is_read_only_handle_name` (or export it), then re-run the three specs above.

## Fix (2026-11-14)

`hir_lowering/types.spl:45` is now `pub fn is_read_only_handle_name`. The seed's rule
(`check_private_call_visibility`, `interpreter_module/module_loader.rs`) lets a private fn be
called from the same directory, so `statements.spl` was fine; the caller in the `_Items/`
subdirectory was the one refused.

Seed `simple-covexpr-20261114/build/seed-base/simple`, at `3a99130752c`:
`nil_unit_type_spec` 4 of 6 before, 6 of 6 after; `contextual_enum_payload_spec` 25 of 25 after.
