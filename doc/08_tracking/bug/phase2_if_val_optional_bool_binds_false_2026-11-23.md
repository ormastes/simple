# Phase 2: `if val x = <bool?>` binds `false` when the value is `true` (2026-11-23)

Status: FIXED-IN-SOURCE (takes effect from the next compiler built from this source;
already-built Phase 2/3 binaries keep the defect)
Compiler: fresh Windows Phase 2 `stage2-admitted/simple.exe` (`baa8d0d5…`, from `8dae652711e`)

## Symptom

A Phase 3 compiler built by this Phase 2 fails the HIR-cache self-check on every
module whose `HirModule.local_annotation_provenance` holds a `true` entry:

```
[hir-cache] SELFCHECK FAILED module=src/compiler/bootstrap_admission/stage2_module_path_naming.spl ... reason=reencode line=24351 field=1 expected=1 got=0; entry not stored
```

Line 24351 of the quarantined blob is the bool of pair `(38, 1)` in the trailing
`local_annotation_provenance` dict (`37` entries; `38` and `59` are true). Encode wrote
`1`; decode followed by re-encode wrote `0`. The store is refused, so this costs cache
reuse but is not fatal.

## Affected source shape

Generated decoder `src/compiler/20.hir/generated/hir_codec.spl` (release tree lines
6087, 6098, 7165; the `Dict<_, bool>` maps `method_return_is_array`,
`method_return_is_optional`, `local_annotation_provenance`):

```
val dv37 = if raw39 == "N": nil else: raw39 == "1"
if val present_v37 = dv37:
    f_local_annotation_provenance[dk37] = present_v37
```

## Minimal repro (compiled by Phase 2, hello-sanity flags)

```
dec_a: val dv = if raw == "N": nil else: raw == "1"; if val present = dv: d[38] = present
dec_b: if raw != "N": val flag: bool = raw == "1"; d[38] = flag
```

Output: `lit=1 dec_a=0 dec_b=1 has_a=true`. The binding takes the then-branch
(`has_a=true`) but the stored value reads back false.

## Root cause

The `if val` binding is correct for a TYPED `bool?` (annotated local or parameter): the
present branch decodes the payload as bool and `d[k] = b` boxes it with the bool tags
(11 / 19). The defect is the UNTYPED join `val dv = if c: nil else: <bool expr>`.

`join_untyped_optional_arms` (`src/compiler/50.mir/mir_lowering_stmts.spl`) types such a
join as `T?` only when every bare `T` arm passes `optional_join_bare_payload_ok`, which
admitted text and nominal heap handles but rejected every scalar ("its raw word could
equal the nil sentinel 3"). The bool arm also had no registered HIR type at all (a
comparison result has a MIR `Bool` slot only), so the join hit "an arm has no type" and
left `dv` an untyped raw word (3 / 0 / 1). With no `bool?` type on `dv`, the ExistsCheck
recorded no `Bool` on the binder, `present` stayed a bare i64, and `d[38] = present`
boxed it through `rt_value_int_wide` as the INT 1. Read back as a bool (`== 11`), int 1
is false.

Lowered MIR before the fix (seed-interpreted compiler source, same as Phase 2's lowering):
the store branch is `Cast; Shl 3; rt_value_int_wide; rt_dict_set`. Annotated `bool?`:
`Eq 1 | Eq 11` decode, then `* -8 + 19` bool box.

## Fix

- `optional_join_bare_payload_ok`: admit `Bool`. A bool word is 0/1 (tagged 11/19),
  never the sentinel 3, so normalising it to `bool?` at runtime is exact. Int / char /
  float stay rejected (the 3 collision is real for them; `classify_option_word` also
  rejects float slots).
- `join_untyped_optional_arms`: an arm with no HIR type but a MIR `Bool` slot is
  recorded as `bool` before classification.

All six join call sites (if, if-chain, match) route through this helper.

## Specs

`test/01_unit/compiler/50.mir/if_val_untyped_optional_bool_join_spec.spl`:

- Reproducer: the exact hir_codec shape binds a bool (bool box constants 11 / 19
  present) and the join is normalised (`rt_enum_id`).
- Generalisation: reversed arm order (`if c: flag else: nil`), elif chain
  (`nil elif ...: true else: false`).
- Controls: annotated `bool?` local, `bool?` parameter, and an untyped nil / int join
  that must stay unnormalised.

On the old source 4 of 7 fail (all four untyped-join cases) and the 3 controls pass. On
the fixed source 7 of 7 pass. With only the `Bool` admission (the MIR-Bool arm registration
disabled) the same 4 fail, so both edits are required. Run with the Phase 1 seed interpreter; the seed reproduces
the defect because it interprets the same MIR lowering source.

## Generator

No change to the `hir_codec.spl` generator is needed: the compiler fix covers the
generated shape. The private-tree workaround (`dec_b` form in `/c/dev/simple-p3-w22`) is
not applied here.

## Other `if val` on `bool?` sites in src/compiler

- `src/compiler/20.hir/generated/hir_codec.spl:6087, 6098, 7165` (the untyped joins
  above; fixed by this change).
- `src/compiler/99.loader/loader/compiler_sffi.spl:947` (`opt: bool?` parameter) and
  `:963` (`val opt = sffi_json_field_bool_opt(...)`, a declared `bool?` return): typed,
  already correct.
- The other `val f_* = if rawN == "N": nil else: rawN == "1"` hir_codec fields are not
  `if val` bindings; they now also join to `bool?`.
