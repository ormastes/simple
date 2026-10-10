# Two value structs embedded themselves by value (TypeInfo.elem, ShellCommand.pipe_to)

Date: 2026-10-10. Found by phase 4 (stage 2 building the full CLI, 2523 modules):

    [post-hir-validation-fatal] recursive by-value struct layout: TypeInfo.elem -> TypeInfo

printed after ~100 minutes of HIR lowering, with no module, file or line.

## Declarations (true positives) — fixed

- `struct TypeInfo` (`src/compiler/99.loader/loader/compiler_sffi.spl`) had `elem: TypeInfo`.
- `struct ShellCommand` (`src/compiler/15.blocks/blocks/value.spl`) had `pipe_to: ShellCommand`.

Both came from rewriting an optional field `x: T?` as `has_x: bool` + `x: T`. That
pair is only well-formed when `T` is a reference type; for a `struct` it embeds
the value in itself. The seed never noticed: it boxes every struct, stores `nil`
in the slot, and its deep-copy descriptor stops on a repeated type name
(`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs`, `struct_deep_fields`).

Only one type named `TypeInfo` is declared under `src/`; this was not a
same-named-type confusion. A name-based scan of every `.spl` under
`src/compiler`, `src/app`, `src/lib`, `src/plugins` and `examples/10_tooling`
for by-value struct cycles of any length finds these two and no others.

Fix: the field is a zero-or-one-entry array (`elem: [TypeInfo]`,
`pipe_to: [ShellCommand]`), still gated by `has_x`. `[T]` is how every other
self-referential struct field in `src/compiler` is spelled (9 of 9; no struct
uses `T?` or a class for this), and `TypeInfo.args` already used it.
`generated/ast_semantic_value.spl` was regenerated with
`simple run src/app/compiler_schema/main.spl folds`, not hand edited.

One difference no reader can observe: a decoded type without an `elem` used to
carry a `default_type_info()` placeholder in the slot and now carries `[]`.

Stage-2 run-tree workaround tag (same edit, applied before this landed):
`WORKAROUND(stage2:recursive-struct-layout-typeinfo, BUG-recursive_struct_layout_typeinfo_2026-10-10)`.

## Verification

Seed, `test/01_unit/compiler/loader/`: nested_type_json 2/2 and
structural_type_cache_key 3/3 (both exercise `elem`), concrete_type_tag 3/3,
json_escape 2/2, type_encoding_bounds 3/3. `json_string_roundtrip` and
`json_structural_scanner` each fail 1 of 3 — identically on the unmodified
tree (JSON escape decoding, unrelated to this change).
