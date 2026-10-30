# MIR enum payload / match-owner identity failures in whole-program stage3 (2026-10-25)

Status: OPEN — triaged, root cause NOT proven, no compiler change landed.

## Evidence

Source log (read-only): `C:/dev/wt-rel3-new/build/s3-bis-new/build.log`
(+ `mir-summary.txt`), whole-program stage3 MIR lowering at `10dffd62fb4`.
The lowering was executed by the stage2 binary
(`.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-gnu/simple.exe`,
provenance receipt 2026-10-24 22:38, binary 2026-10-25 07:36), so the MIR
code that emitted these errors predates #4528/#4536/#4537/#4543 and every
2026-10-25 MIR fix. The counts below are an upper bound for current source.

| class | count | emitter |
|---|---|---|
| `enum construction '<Q>.<V>': payload type mismatch at N` | 2760 | `50.mir/_MirLoweringExpr/enum_constructor_payload.spl` `enum_payload_mismatch_message` |
| ... of which `payload_at=:0:0` (expression span empty) | 1550 | |
| `enum match: pattern owner X does not match subject owner Y` | 81 | `switch_operators_calls.spl:4041` |
| `enum match: bare variant X is ambiguous` | 58 | `switch_operators_calls.spl:2463` (Ok 22, Tuple 8, Struct 8, Str 4, Int 4, ...) |

Representative payload mismatches where the payload is trivially well typed:

- `fn toplevelitem_StaticAssert(item: StaticAssertOutline) -> TopLevelItem: TopLevelItem.StaticAssert(item)` (`10.frontend/treesitter/outline.spl:34`) — a parameter of the exact declared type.
- `MirOperandKind.Copy(LocalId(id: x))` in `60.mir_opt/_OptimizationPasses/io_passes.spl:402` (MirOperandKind imported through the `mir_instructions` facade, `LocalId` from `mir_types`).
- `TextIoError.Transport(IoError(...))` in `lib/nogc_sync_mut/io/file_text_session.spl:26` (`IoError` imported as `std.io.types`, declared in `src/lib/common/io/types.spl`).
- `HirChildFrame.Expr(it0)` in `20.hir/generated/hir_children.spl` — own enum, payload from an array element / match binding.

Owner-mismatch pairs are nonsensical (`HirBinOp` vs `LayoutPhase` x19,
`BinOp` vs `EffectKind` x11, `MirConstValue` vs `OptimizationLevel` x8): the
subject's `Named(SymbolId)` is being read through a symbol table that did not
allocate it.

## Ranked hypotheses (all one family: SymbolId read in the wrong table / owner spelling not folded)

1. **Foreign-table IDs in payload/subject HirTypes.** The owner-mismatch pairs
   are only explicable this way. Candidates: `enum_variant_payload_types`
   persisting across modules outside the declaration-repository lane
   (only reset at `module_lowering.spl:2496` when `declaration_repository != nil`),
   and remembered local HIR types carried from an archived/lifted lowerer
   (`switch_operators_calls.spl:7749` adopts `lw.symbols`).
2. **Owner-spelling split for one declaration.** `register_imported_symbol`
   (`module_import_registration.spl:~600`) compares `existing_owner ==
   imported_mod.module_name` raw and allocates a second `"{owner}::{name}"`
   symbol on mismatch; `hir_symbol_owner_module` folds digit tiers and
   `std.`->`lib.` but not std layer search (`std.io.types` ->
   `lib.io.types` vs declared `lib.common.io.types`). `enum_payload_named_alias_equal`
   then rejects the pair on owner.
3. Bare-variant ambiguity (58) is the expected fail-closed diagnostic for
   `Ok`/`Tuple`/`Struct`/... when the subject type is unknown; it shrinks only
   when subject typing (1) is fixed.

## Why no fix landed

No runnable repro on the Windows host: `bin/simple.exe` is the Rust seed; the
stage2 binary refuses a two-module `native-build --entry-closure` repro with
`SCV-E-ADMISSION: derived-composition-identity-mismatch` (and outside a git
checkout, `compile-event-journal-missing` / `HIR cache identity unavailable`).
Relaxing `enum_payload_named_alias_equal` without proof would accept genuine
mismatches, violating the fail-closed contract.

## Next step (cheap, decisive)

Re-run the stage3 MIR phase with a stage2 built from current release source and
`SIMPLE_ENUM_PAYLOAD_TRACE=1`; each `[enum-payload]` line names expected vs
remembered/source/MIR evidence. `expected` and `remembered` with the same shape
key ⇒ hypothesis 2 (owner split); different names ⇒ hypothesis 1 (foreign IDs).
