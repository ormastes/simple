# A struct value whose MIR type is the erased I64 is boxed as a wide int
## Open 2026-10-25. MIR guard in `box_runtime_value`; takes effect on the Phase 3 self-rebuild

Date: 2026-10-25. Lane: Phase 3 bootstrap (run-27e), the B6a/B7/B8 class, compiler-fix agent.

## Symptom

Stage-2-emitted code passed struct values through `rt_value_int_wide`
(`ptr << 3`) before `rt_dict_set` / `rt_array_push`:

- B6a: `module_build lower_module:571`, `val fn_key = if ..: real_id else: SymbolId(..)`
- B7: `if val present = opt: arr.push(present)`
- B8: 36 struct pushes in `mir_array_move.am_children`

The bypass agent NOPs the calls by binary patch.

## Root cause (B6a, measured)

`box_runtime_value` (`50.mir/_MirLoweringExpr/expr_dispatch.spl`) chooses the
box from the local's MIR type alone. Its I64/U64 arm calls `rt_value_int_wide`.
An untyped value-position `if` whose arm is a struct-returning CALL result
keeps an I64 result type, so the struct handle takes the integer arm.

Stage-2 disassembly of the repro: the untyped function calls
`rt_value_int_wide(k)` and then `rt_dict_set(d, boxed, ..)`. The annotated twin
(`val k: K = ...`) has a Struct-typed local and passes `k` straight through.
The source is current: Stage 2's 50.mir source (5c9ddef0f1b) matches d3fc
here.

## Fix

Before choosing a box, `box_runtime_value` asks
`box_runtime_value_local_is_record`. A local is returned untouched (as the typed
path already does) when it has struct-name provenance
(`struct_value_syms`) whose name has a registered record layout
(`struct_field_order`), or a remembered HIR type naming a Struct/Class
symbol.
Excluded: bitfields (`bitfield_value_syms` / `bitfield_map`; they are
`SymbolKind.Struct` but are integer words), newtypes over a primitive
(`custom_primitive_underlying_type_tag_*`; also `SymbolKind.Struct`, lowered to
I64/F64/Bool), generic-parameter sentinels in `struct_value_syms`, and enums
(unit variants may be
immediates).

## Verification and limits

- Red: Stage 2 builds `native_record_local_not_int_boxed_spec.spl`'s fixture.
  It SEGVs, and `rt_value_int_wide(k)` precedes `rt_dict_set` in the disassembly.
- Green: deferred to the Phase 3 self-rebuild. Not proven: that the B7/B8
  locals carry `struct_value_syms` or a Named HIR type at the boxing point.
  The guard only fires where that provenance exists. A plain
  `if val p = maybe(): xs.push(p)` into a typed `[K]` was NOT int-boxed on
  Stage 2. That repro SEGVs for a different, unrecorded reason.
- B9 (generic `$i64` instance) is a separate, source-visible bug:
  `enum_discriminant_i64_instance_int_boxes_enum_2026-10-25.md`.
- Known residual (review P2): `custom_primitive_underlying_type_tag_by_name` is
  keyed by the bare declared name, while `struct_field_order` may hold a
  qualified `owner::Name` layout key. A newtype that reaches `struct_value_syms`
  under a qualified key would pass the name branch. Typed locals are still
  rejected by the by-symbol check.
- The guard needs the provenance name to be a registered layout key. Some
  `struct_value_syms` writers store a bare name, so the guard may not fire for
  those. No green run exists for any variant yet; that comes only on the
  Phase 3 self-rebuild.
