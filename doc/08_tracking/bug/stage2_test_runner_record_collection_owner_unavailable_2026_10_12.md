# Stage 2 test runner cannot rebind exact record collection provider

- **ID:** `stage2_test_runner_record_collection_owner_unavailable_2026_10_12`
- **GitHub:** #3298
- **Severity:** P1
- **Status:** fix-implemented-verification-pending (2026-11-08)
- **File:** `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  (`rebind_record_element_owner` -> `rebind_named_type_owner`)
- **Reproducible by:** `native-build src/app/test_runner_new/main.spl --backend=llvm --low-memory --timeout 600 --threads 8`
  (frozen stage2 compiler compiling the test runner; the seed interpreter does
  not exercise this path)

## Symptom

The Stage 2 MIR build of the test runner visits 252 modules and then fails the
whole build with the strict ownership refusal

```
record collection payload owner is unavailable in the consumer: owner=<provider::Type> ...
```

(earlier wording: "unavailable exact record owner"). The aggregate MIR/object
never reaches PASS. The diagnostic-only patch recorded in the triage history
kept strict ownership and added provider/consumer/symbol/span evidence; it did
not change the producer. A prior lane established the failure is native-only.

## Root cause (workaround-first analysis, 2026-11-08)

`rebind_named_type_owner` is the last lookup before the refusal. Its final
fallback bound a struct-valued Option across a function boundary:

```
if val present_rebound = self.symbols.lookup_exact_type(bare_name):
    val rebound: SymbolId = present_rebound
    if self.symbol_matches_ownership_key(rebound.id, owner_key): ...
```

That is a known frozen-stage2 miscompiled shape: staged native code corrupts a
value-type `SymbolId` carried inside `Optional` across a call boundary even
though the exact dictionary entry is valid (documented on
`SymbolTable.lookup_qualified_type_raw`, which was made scalar for exactly this
reason, and on `symbol_name_scalar_raw`). `lookup_exact_type` itself
additionally round-trips `HirSymbol?` via `get_symbol_raw`. When the imported
record element's exact owner is present in the consumer table, the corrupted
Option reads as a miss (or as a foreign id that then fails
`symbol_matches_ownership_key`), `rebind_named_type_owner` degrades to `Error`,
and `rebind_record_element_owner` correctly refuses the "unavailable" owner --
on a provider that was in fact available.

The three readers of the provider ownership-key table feeding that path shared
a second bad shape: a class-field `Dict<text, [text]>` bracket-read bound to a
`[text]?` local, tested with `!= nil` and rebound with `if val`.

## Fix (2026-11-08, lane `lane-f-trrecord`, branch `work/fix-test-runner-record-owner-20261108`)

Source workaround in the code stage2 compiles; strict ownership is retained
(no silent pass-through was added).

- `src/compiler/20.hir/hir_symbol_table_methods.spl`: new
  `SymbolTable.lookup_exact_type_raw(name) -> i64` (-1 on miss). Scalar twin of
  `lookup_exact_type` on the proven Dict bracket path; transports neither
  `HirSymbol?` nor `SymbolId?`.
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  - `rebind_named_type_owner`: the exact-owner fallback now uses
    `lookup_exact_type_raw` and compares the raw id; the whole chain is scalar.
    Tag: `# @workaround bug=stage2_test_runner_record_collection_owner_unavailable_2026_10_12 reason=stage2_native_corrupts_SymbolId_option_across_lookup_exact_type_boundary`
  - new `struct_field_ownership_key_at(owner, field_idx) -> text` replaces the
    three duplicated `[text]?` / `!= nil` / `if val` readers
    (`declared_field_type_in_current_table` Optional and Named arms,
    `declared_record_array_element`); binds the array to a typed local behind
    `contains`. Tag: `# @workaround bug=... reason=stage2_native_miscompiles_option_array_bound_via_if_val_from_class_field_dict_bracket_read`
- `src/compiler/50.mir/_MirLoweringExpr/builtin_method_extras.spl`: the
  sibling Result-payload rebind had the identical `if val rebound =
  self.symbols.lookup_exact_type(...)` shape; converted to the scalar lookup
  with the same tag.

### Specs

- `test/01_unit/compiler/bootstrap/stage2_record_owner_scalar_lookup_spec.spl`
  (new; 6 examples): behavioural pins for `lookup_exact_type_raw` (hit on
  Struct/Class/Enum, -1 on absent name and on a Function symbol, agreement with
  the Option form) plus source-shape guards that the rebind, the sibling
  rebind, the ownership-key readers and the new method stay on the scalar /
  typed-local shapes. Before fix: `6 examples, 6 failures`. After fix:
  `6 passed, 0 failed`.
- Regression (unchanged, green after the fix):
  `test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl` (3/3),
  `test/01_unit/compiler/50.mir/enum_field_eq_lowering_spec.spl` (6/6),
  `test/01_unit/compiler/50.mir/provider_layout_demand_spec.spl` (4/4).

### Unverified

Native verification is pending: the miscompile is only observable when the
frozen stage2 binary compiles the test runner (`native-build
src/app/test_runner_new/main.spl --backend=llvm`). The interpreter-run specs
above prove the scalar lookup's semantics and freeze the source shape; they
cannot prove the 252-module build now passes. Status therefore stays
`fix-implemented-verification-pending` until the leaf-58 native binary runs it.

`src/compiler/50.mir/_MirLowering/provider_metadata.spl:76` still uses the
Option `lookup_exact_type` (followed by a `get_symbol_raw` Option); it is a
different owner path (provider method receiver check) and was left unchanged
and is noted here for the next native run.
