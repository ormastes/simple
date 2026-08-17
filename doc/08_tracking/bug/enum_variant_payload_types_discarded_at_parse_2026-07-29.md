# Enum variant payload types are discarded at parse time — MC-API enum-payload lint (A4) structurally blocked

- **Filed:** 2026-07-29 (lane A4E `semantic-enum-payloads`)
- **Severity:** Medium — blocks a documented mission-critical lint gap (A1's
  `semantic_api` recursive primitive-API checker cannot fire on enum variant
  payloads); no runtime-correctness impact by itself.
- **Component:** compiler frontend — enum declaration parsing
  (`10.frontend/core/parser_decls_types.spl`,
  `10.frontend/core/_ParserDecls/enum_module_body.spl`) and the flat-AST bridge
  (`10.frontend/_FlatAstBridge/module_assembly.spl`).
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  require parser + decl-arena + bridge changes, none of which A4E is
  authorized to touch).

## Ground truth (file:line evidence)

A1 (`src/compiler/35.semantics/lint/semantic_api/checker.spl` header) already
recorded that enum payloads are "NOT covered" and asked A4 to verify whether
the flat AST carries payload type nodes. It does not, at any layer:

1. **Parser throws the type away at the token level.** Both enum-decl parse
   paths call `parser_parse_type()` for a variant's payload field purely to
   advance the token stream; the return value is never assigned or stored:
   - `src/compiler/10.frontend/core/parser_decls_types.spl:140` —
     `parser_parse_type()` (bare statement, result discarded) inside the
     `Variant(field: type, ...)` loop (comment at line 127).
   - `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:150` and
     `:155` — same pattern, the module-level `enum X:` variant-list parser.

2. **The decl arena has no payload slot to store it in even if it wanted to.**
   `decl_enum_def(name: text, variant_names: [text], variant_discriminants: [i64], span_id: i64) -> i64`
   (`src/compiler/10.frontend/core/_Ast/decl_nodes.spl:586`) takes no type
   parameter at all — only names and discriminant expression ids.

3. **The one real production bridge from decl-arena to AST hardcodes empty
   payloads for every real enum.**
   `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:370-405`
   converts `tag_text == "8"` (enum) decls into `compiler.core.ast.Enum` /
   `Variant` nodes and explicitly sets `kind: VariantKind.Tuple([])` for
   every variant (line 390), with the inline comment (lines 372-375):
   "Payload types are not stored in the flat AST, so kind is Tuple([])."
   This is the ONLY site in the tree that builds `Enum`/`Variant` AST nodes
   from real parsed source (no other `Node.Enum(`/`Enum(` construction site
   exists outside this file, test fixtures, and the unrelated generic-template
   cache below).

4. **HIR (a later, richer, fully-typed stage) inherits the same emptiness.**
   `HirVariantKind.Tuple(types: [HirType])`
   (`src/compiler/20.hir/hir_definitions.spl:196-199`) CAN represent real
   payload types, but `lower_variant`
   (`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:728-743`)
   only ever receives the already-empty `[]` produced by step 3 for a genuine
   user-declared enum. So even HIR carries no real payload types for enums
   parsed from ordinary source.

5. **The `compiler.frontend.ast.EnumDef.variants: [text]` field CAN encode
   payload text** (used by `40.mono/monomorphize/deferred_subst.spl:318-343`
   `_specialize_enum_def`, whose docstring says it substitutes type params
   "in variants (variant type annotations)", and the illustrative comment at
   `deferred.spl:668` shows `variants: ["Some(Int)", "None"]`) — but this is a
   separate generic-template specialization/serialization cache
   (`.smf` template round-trip: `deserialize_enum_def` in
   `deferred_deserialize.spl:360-393` only round-trips bytes previously
   serialized). No construction site for the *original* (non-specialized)
   template `EnumDef` from real source was found anywhere in the tree — i.e.
   nothing was found that populates that text with genuine parsed payload
   types for a first-generation enum declaration. This path is unproven/dead
   for the purpose of recovering payload types and should not be relied on.

## Conclusion for A4

Enum variant payload types are discarded at the parser itself (step 1) and
never reconstructed anywhere downstream that a semantic checker over the
production AST (flat or HIR) could consume (steps 2-4). There is no AST
structure available to lane A4E's checker
(`src/compiler/35.semantics/lint/semantic_api/{type_walk,checker}.spl`) to
walk — this is not a lossy-tag recovery problem (A1's original framing), it is
a genuine "never stored" problem one layer earlier, at the parser.

## What would actually fix this (out of scope for A4E)

Store parsed payload types in the decl arena (extend `decl_enum_def` with a
per-variant type-text or type-id list, mirroring how struct/class fields
already carry `"name: Type"` text) at
`parser_decls_types.spl:140`/`enum_module_body.spl:150,155`, thread it through
`decl_get_fields`-equivalent accessors, and stop hardcoding
`VariantKind.Tuple([])` in `module_assembly.spl:390`. That is a parser +
decl-arena + bridge change, well beyond a `semantic_api/` lint-layer edit, and
touches files A4E's ownership charter explicitly excludes.

## This lane's outcome

No functional change to `type_walk.spl`/`checker.spl` — the enum arm in
`checker.spl.check_module_items` (`case Enum(_): pass`) is correct as-is given
the ground truth above; its comment was updated to point at this bug doc
instead of only describing the (now superseded) "lossy tag" theory. One spec
example was added confirming the current, honest behavior (a clean/any enum
emits nothing) so the gap stays test-visible instead of silently assumed.
