# Enum decorators are accepted by the parser but never reach HIR

- **Date:** 2026-08-21
- **Status:** FIXED (channel to HIR) 2026-08-21; symptom (1), rejecting an
  unrecognised decorator name, is deliberately NOT fixed — see Resolution
- **Found by:** S2/S3 enum-contract work (hardening plan
  `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` §10.1/§10.2)
- **Binary:** `bin/simple` (Rust seed; `--version` prints the seed warning banner)

## Symptom

A decorator on an `enum` declaration parses and runs cleanly, but the
annotation is unavailable to any later pass. Two things are wrong at once:

1. **No validation.** An entirely made-up decorator is accepted silently:

   ```simple
   @totally_bogus_decorator_xyz
   enum Color:
       Red
       Green

   fn main():
       print("ok")
   ```

   `bin/simple run` on this prints `ok`, exit 0. The same holds for the two
   decorators §10 specifies, `@closed` and `@evolving(repr: u16, unknown: Unknown)`.

2. **No channel to HIR.** `HirEnum`
   (`src/compiler/20.hir/hir_definitions.spl:204`) has no `decorators` /
   `attributes` field — it carries only `symbol`, `name`, `runtime_name`,
   `type_params`, `variants`, `visibility`, `is_public`, doc-comment and
   generic-template metadata. `/usr/bin/grep -rn decorators src/compiler/20.hir/`
   returns **zero** lines. The only `decorators` machinery in the frontend is
   `parser_reset_pending_vhdl_decorators` in
   `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:554`, which
   is VHDL-specific. So the decorator is dropped between parser and HIR.

Consequence: a semantic pass cannot ask "is this enum `@closed`?" at all. Any
enum-contract enforcement must recover the annotation from some other channel.

## Impact

Blocks the intended wiring of S2/S3. The checker landed in
`src/compiler/35.semantics/enum_contract/` therefore recovers the contract
table by scanning the module's SOURCE TEXT
(`enum_contract/attribute_source.spl`), which is a workaround, not the design.
It is isolated to one function so the fix is a one-line change at the call
site once the decorator reaches HIR.

More broadly, symptom (1) means **every** misspelled decorator anywhere in the
tree is silently ignored rather than rejected — a `@clsoed` typo disables a
safety contract with no diagnostic.

## Unblock condition

1. `HirEnum` gains a decorator/attribute field, and HIR lowering populates it
   from the enum's parsed decorator list.
2. The parser rejects (or at minimum warns on) an unrecognised decorator name.

Then replace the body of `read_module_source` / the first line of
`enum_contract_check` (`src/compiler/35.semantics/enum_contract/check.spl`)
with a table built directly from `module.enums`, and delete
`attribute_source.spl`.


## Resolution (2026-08-21)

The channel now exists end to end.

- **Parser** (`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`):
  the module-body decorator arm records every decorator on
  `PENDING_DECL_ATTRS` as a raw spelling (`closed`,
  `evolving(repr:u16,unknown:Unknown)` — arguments rebuilt from the token
  texts the arm already walks, whitespace removed), cleared per declaration by
  `parser_reset_pending_vhdl_decorators` exactly like `PENDING_UNSAFE_*`. The
  enum arm calls `parser_record_enum_attributes(decl_get_name(d))`;
  `parser_enum_attributes_for(name)` exposes them.
- **AST**: `ParserEnum.attributes: [text]`, added as the LAST field.
- **HIR** (`src/compiler/20.hir/hir_definitions.spl`): new `HirAttribute`
  (`name`, `args`), `HirEnum.attributes: [HirAttribute]` as the LAST field, and
  helpers `hir_enum_has_attribute` / `hir_enum_attribute_args` /
  `hir_attribute_from_raw`. Populated in
  `hir_lowering/_Items/declaration_lowering.spl:lower_enum_with_symbol`.
- **Consumer**: `src/compiler/35.semantics/enum_contract/attribute_source.spl`
  gains `enum_contract_table_from_hir(enums)` plus `contract_of_attribute`,
  which read the annotation itself. `enum_contract_table_from_source` is kept
  unchanged in behaviour and signature for the callers that hold only source
  text (`check.spl`'s `read_module_source` path and the specs).

**Unknown decorators are PRESERVED, not rejected.** Other lanes own their own
decorator vocabularies, so the parser cannot hold the closed vocabulary that
symptom (1) asks for. A `@clsoed` typo now reaches HIR as an attribute named
`clsoed`, where a lane that owns the `closed` vocabulary can diagnose it; that
diagnosis is not implemented here.

### Evidence

New spec `test/01_unit/compiler/hir/enum_attributes_spec.spl` (mirrored to
`test/unit/compiler/hir/`): `Results: 7 total, 7 passed, 0 failed`. It proves
`@closed` is recorded, two decorators survive in source order including a
bogus one, `@evolving(repr: u16, unknown: Unknown)` arrives as
`evolving(repr:u16,unknown:Unknown)`, and an undecorated enum has none.

Enum-contract specs stay green: closed `14 total, 14 passed`, evolving
`18 total, 18 passed`, discriminant roundtrip `10 total, 10 passed`.

Five existing HIR specs, run before and after the change on the same binary
(`bin/release/x86_64-unknown-linux-gnu/simple`) — identical either side, so no
regression:

| spec | before | after |
|---|---|---|
| `alias_static_call_resolution` | 2 total, 0 passed, 2 failed | 2 total, 0 passed, 2 failed |
| `bootstrap_hir_store` | 5 total, 2 passed, 3 failed | 5 total, 2 passed, 3 failed |
| `domain_block_hir_lowering` | 3 total, 3 passed, 0 failed | 3 total, 3 passed, 0 failed |
| `class_method_bodies_reachable` | (green) 3 total, 3 passed, 0 failed | 3 total, 3 passed, 0 failed |
| `field_index_erased_receiver` | 1 total, 0 passed, 1 failed | 1 total, 0 passed, 1 failed |

### Found while fixing: HIR enum lowering returns nil under the seed

`HirLowering.lower_enum(...)` / `lower_module(...)` return a nil `HirEnum` for
ANY enum under the Rust seed — verified on unmodified HEAD with the change
stashed, so it predates and is independent of this work. That is why the new
spec asserts the HIR half on a directly constructed `HirEnum` rather than by
calling the lowering entry point. Anyone wiring
`enum_contract_table_from_hir` into a live pass must clear that first.
