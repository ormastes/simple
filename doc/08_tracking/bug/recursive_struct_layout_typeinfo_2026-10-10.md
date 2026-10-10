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

## Validator: false negative on the retained HIR path — fixed

Phase 3 (same stage-2 binary, same module in its 1160-module closure) printed
`phase3:hir:validate:value_struct_layouts:done errors=0`; phase 4 printed
`errors=1`. Phase 4 runs with `SIMPLE_STAGE4_STREAMING_SURFACES=1`. An 8-line
file (`struct Node: name: text; has_elem: bool; elem: Node`) built with the
frozen stage 2 on the retained path also reported `errors=0`.

Cause (`src/compiler/35.semantics/value_struct_layout.spl`). The walk turned a
field's struct symbol into a graph node as `<symbol.defining_module>|<name>`
and looked that up among nodes keyed `<module key>|<name>`. Module keys are
LOGICAL names (`surfaces[i].logical_name`). `defining_module` is whatever the
definer passed, stored verbatim by `SymbolTable.define`:

- a module's own declarations pass `HirLowering.module_filename`, the SOURCE
  PATH (`declare_module_symbols`, `begin_module(source.path)`);
- symbols registered from an import surface pass the logical name.

Only the second spelling could match, so an edge to a struct whose symbol came
from its own declaration was dropped by `if not structs.has(target): continue`.
A struct embedding itself was therefore reported only when its symbol happened
to have been prebound from a surface first — which is what the streaming
closure did for `TypeInfo`, and why the result differed by pipeline rather than
by source. This is not an ordering problem: no path desugars `T?` after
validation (see below); it is an identity-spelling mismatch.

Fix: two exact indexes, no path normalization.
1. `"<module index>:<symbol id>"` -> node, for every struct a module declares.
   A field whose symbol id is one of its owner's own structs resolves by id,
   independent of the owner text.
2. `HirModule.path` -> module key, tried when the owner text is not a key.

Proof is at unit level, test first: `value_struct_layout_spec.spl` gained
REQ-SEM-VSL-014 (path-spelled self-cycle, logical-spelled self-cycle, owner
text matching nothing, cross-module cycle with path-spelled imports, and a
path-spelled non-cycle that must stay clean). Three of those five failed on
the old validator. NOT proven natively: re-running the 8-line repro needs a
stage 2 rebuilt from this source.

Consequence to expect: the retained path now really enforces the rule. Any
program outside the scanned roots that embeds a struct in itself by value was
compiling by accident and will be rejected.

Residual: an edge to a struct symbol that resolves to no known module (neither
key nor path, not an own struct) is still skipped silently, as is recursion
through a generic instantiation (`Box<Node>`, pinned as REQ-SEM-VSL-008).

## Validator: diagnostics — fixed

- Reports every cycle in one run (was: first only, i.e. one ~100-minute round
  per cycle). A mutual cycle is reported once, from its first root.
- Each diagnostic now ends with the location of every hop:

      recursive by-value struct layout: TypeInfo.elem -> TypeInfo [struct TypeInfo in module compiler.loader.loader.compiler_sffi at src/compiler/99.loader/loader/compiler_sffi.spl:413, field elem at src/compiler/99.loader/loader/compiler_sffi.spl:429]

  The prefix is unchanged, so `native_build_main.spl`'s
  `[post-hir-validation-fatal` scan and log summarizers keep matching.
  Locations are built only when a cycle closes; a healthy build reads no span.

## Should `x: T?` on a self-recursive struct get an indirection automatically?

There is no live desugar to change. `# # DESUGARED:` (190 markers in
`src/compiler`) is the residue of a one-time SOURCE rewrite that replaced
`x: T?` with `has_x: bool` + `x: T`; no tool in the tree performs it now, and
neither the seed nor the pure-Simple compiler rewrites optional fields. Both
lower `x: T?` to an Optional type, and the validator already treats Optional
(and `[T]`) as an indirection, so a user writing `next: Node?` never hits this
check. The seed goes further and boxes every struct, which is why the
hand-rewritten `x: T` form ran at all.

Recommendation: do not add automatic indirection for a bare by-value `x: T`.
It would give `struct` two layouts depending on whether a cycle exists, and
hide a real size error. Keep the rule "a struct may not contain itself by
value" and keep it enforced (now on both paths). Two follow-ups are worth
doing, neither done here:
- make the diagnostic suggest the fix (`T?` or `[T]`) when the field has a
  sibling `has_<field>: bool`, since that pair is the signature of the old
  rewrite;
- confirm Optional-of-struct fields are sound in stage-2 native code before
  recommending `T?` over `[T]` in this tree — every self-referential struct
  field in `src/compiler` uses `[T]`, and Option-of-aggregate was the fragile
  ABI shape the old rewrite was avoiding.
