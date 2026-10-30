# Member visibility policy exists but HIR lowering never enforces it

- Date: 2026-10-26 | Owner area: src/compiler/20.hir/hir_lowering + 00.common/dependency | Size: M
- Symptom: test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl 11/17 fail, all "compile-rejects ..."
  (`expected false to equal true` from `messages_contain(errors, "field \`secret\` is not visible")`,
  "aggregate constructor \`Vault\` is not visible", etc.). The "compile-allows" cases pass trivially.
- Evidence: policy helpers `member_visibility_allows`, `aggregate_constructor_visibility_allows`,
  `member_access_scope_for_modules` (src/compiler/00.common/dependency/member_visibility.spl:71,106,122) are only
  exported (dependency/__init__.spl:74-76) and used by test/01_unit/compiler/dependency/member_visibility_spec.spl.
  No caller in src/compiler/20.hir. No source anywhere emits the diagnostic text "is not visible" for fields
  or aggregate ctors (only a stale comment at 20.hir/hir_lowering/_Expressions/expression_support.spl:241).
  Same on origin/main and origin/release/1.0.0. Field typing (expression_support.spl:225 field_type_for_owner_raw)
  never consults visibility.
- Secondary: peer/up-field tests synthesize sources under `src/compiler/20.hir/...`; log shows
  `[parser_error] ... 1:14: expected Ident, got IntLit '10'` (numbered layer dir `20.hir` lexed as number in a
  generated import path), so layer-path normalization (member_layer_and_tail, member_visibility.spl:47) must not feed
  `20.hir` into source text.
- Repro: `bin/simple.exe test test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl --no-session-daemon`
- Fix: call the policy from field-read lowering and aggregate-constructor lowering, emit the diagnostics the spec expects.

## Resolution (2026-10-27) - NOT FIXED; blocked on a parser/flat-AST prerequisite. Implementation plan

Baseline 6/17. A prototype HIR wiring reached 9/17 (all code reverted; nothing from it is committed), then was
withdrawn because it is unsound without the prerequisite below.

### Blocking root cause (cross-layer, outside 20.hir)
Field visibility never reaches HIR. `ModuleSurfaceField.visibility` is copied from `ParserField.visibility`, but
the flat-AST bridge hardcodes it: `10.frontend/_FlatAstBridge/module_assembly.spl` builds fields through
`flat_parser_field_from_nodes(...)` which sets `Visibility.Private, is_public: false` (lines ~252-282), and the core
parser records no per-field modifier at all (`decl_struct_def` in `10.frontend/core/_Ast/decl_nodes.spl:612` carries
only names/types/defaults/bits). So `pub value`, `pub(up) value`, `pub(package)`, `pub(friend)` all look private.
Measured with the prototype: `pub struct Record: pub value: i64` + `Record(value: 7)` is rejected as
"aggregate constructor `Record` is not visible". Also, parser default is Private and the compiler's own sources
declare most cross-module fields without `pub` (e.g. `ModuleSurfaceField` read in module_import_registration.spl),
so enabling enforcement unconditionally will reject self-hosted sources; needs a migration/ratchet decision first.

### Plan
1. Parser: record per-field visibility in `parse_struct_decl`/class/actor (accept `pub`, `pub(up|peer|package|friend)`),
   add parallel `decl_field_visibility: [[text]]` in `core/_Ast/decl_nodes.spl` (+ `flat_pool_enc/dec`, copy/reset sites,
   `decl_get_field_visibility`), consumed by `flat_parser_field_from_nodes` via `convert_decl_visibility`-style mapping
   (`friend` -> `Visibility.Internal`). Bumps the flat-pool/SPAB cache format version.
2. HIR registration (`20.hir/hir_lowering/_Items/module_import_registration.spl`, right after
   `struct_field_types_by_name[canonical_composite_name] = ...`): compute once per imported composite
   `member_access_scope_for_modules(self.module_filename, pkg(module_logical_name_from_path(self.module_filename)),
   imported_mod.canonical_path, imported_mod.package_name, imported_mod.friends, imported_mod.internal_exports.contains(imported_name))`
   and store scalar verdicts in two new `HirLowering` dicts (`types.spl`, reset in `context_helpers.spl`):
   `member_field_access_allowed: {text: bool}` keyed `"<module>.<Type>#<field>"` and `member_ctor_allowed: {text: bool}`
   keyed `"<module>.<Type>"` (via `member_visibility_allows` / `aggregate_constructor_visibility_allows`). Use string
   interpolation for keys, not 3-operand `+`.
3. Enforcement, in `_Expressions/expression_support.spl`: `check_member_field_visible(base, field, span)` (owner via
   `owner_type_id_for_base_raw` then `field_owner_for_hir_expr`; key via defining_module + "." + name) called in
   `expression_core.spl` Field arm just before `field_type_for_hir_base`; `check_aggregate_constructor_visible(callee,
   spelling, span)` called in the `ExprKind.Call` arm on the lowered callee (spelling = Ident name or last Field
   segment, so aliases report `AliasVault`). Emit via `self.error("field `x` is not visible from this module", span)` /
   `"aggregate constructor `X` is not visible from this module"`. Prototype result: private imported field read, ctor,
   alias ctor, call-result `.secret`, non-parent `pub(up)`, un-exported friend field, re-export owner all passed.
4. Remaining spec gaps independent of the above:
   - "stored nominal call result" (`val v = make_vault(); v.secret`): local `val` bound to a call needs its return type
     recorded in `local_struct_types` (statements.spl ~134-180 only handles `StructName(...)`).
   - "qualified private ctor" (`vault.provider.Vault(secret: 1)`): qualified callee does not lower to the type symbol;
     resolve via `qualified_types`.
   - SFFI case: spec fixture path `src/lib/nogc_sync_mut/sffi/provider.spl` + module `std.sffi.provider` makes
     `module_surfaces_from_modules` fail ("module surface name disagrees with its path derivation ...
     derived=lib.nogc_sync_mut.sffi.provider"); the std alias fold must cover this path or the fixture changed.
   - Numbered-path IntLit: NOT generated source. The spec's own text `use compiler.10.frontend.shared.node.{...}`
     fails in the parser (`expected Ident, got IntLit '10'`); `use` path segments that are integer tokens must be
     accepted by the use-path parser. The two peer-layer specs need that.
5. Verify: spec 17/17; dependency/member_visibility_spec 10/10; dependency/visibility_spec 20/20;
   mdsoc/feature_layer_matrix_spec 16/16; then a self-host lint/lowering sweep to size the existing private-field fallout.

## Progress 2026-10-27: field visibility plumbing landed in the working tree (enforcement still OFF)
- Parser now records per-field visibility (`decl_field_visibility`, text codes, `pub(friend)` = "internal"),
  encoded/decoded in the flat pool (codec `spl-flatpool-v12-field-visibility`, cold cache on first run),
  and `flat_parser_field_from_nodes` sets `ParserField.visibility`/`is_public` (REQ-PARSER-FIELD-VIS-001).
- Spec `frontend/flat_pool_field_visibility_spec.spl`: red 0/4 -> green 4/4.
- Regression: hir/member_visibility_enforcement_spec 6/17 -> 6/17 (unchanged, HIR check not wired);
  dependency/member_visibility_spec 10/10 -> 10/10; flat_pool_codec_roundtrip 18/18; flat_pool_truncation 13/13.
  Pre-existing and unchanged: facet_flat_decl_codec 0/2, frontend_shared_parse_cas_v1 2/4, flat_ast_if_else_bridge executed=0.
- Remaining: HIR enforcement behind opt-in switch, then bulk `pub` migration / ratchet baseline.
