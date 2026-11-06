# `unsafe` capabilities and reason never reach HIR

Date: 2026-08-21
Reporter: agent A5+Y2 (Any hardening)
Status: fix-implemented-verification-pending (2026-11-06)

## Resolution (2026-11-06)

- Block form (`unsafe(capabilities: [...]):`) was already carried on
  release/1.0.0 via `HirBlock.unsafe_caps` (validated in
  `expression_core.spl`, read by `any_escape/checker.spl`); the
  `UnsafeBlock` variant shape was deliberately left unchanged, so none of its
  match sites needed edits.
- Declaration form (`@unsafe(reason:, capabilities:)`) now reaches HIR:
  the parser records `UNSAFE_ANNOTATIONS` by flat decl INDEX (two classes'
  same-named methods no longer collide), the flat-AST bridge rebuilds an
  `unsafe` attribute, and lowering fills the new trailing
  `HirFunction.unsafe_reason` / `unsafe_caps`, reporting unknown names via
  `unknown_unsafe_capability_names`.
- `any_escape` reads the function grant off `HirFunction.unsafe_caps`; the
  profile list is kept for lanes still passing a textual grant (removing
  `type_erasure_functions` / the census scrape is the remaining follow-up).
- Codec regenerated (byte-equality spec passes); cache identities bumped:
  `HIR_CODEC_VERSION` v15, `FLAT_POOL_CODEC_VERSION` v14.
- Seed-verified: `test/01_unit/compiler/hir/hir_function_unsafe_caps_spec.spl`
  4/4 (0/4 on the pre-fix tree). Pending: native/Stage-3 confirmation of the
  cache-version bump.

## The gap

`HirExprKind.UnsafeBlock` carries only a body:

```
src/compiler/20.hir/hir_definitions.spl:569
    UnsafeBlock(body: HirBlock)         # unsafe: ... - unsafe operations
```

No reason, no capability set. Any semantic pass that must ask "does THIS unsafe
region carry the `type_erasure` capability?" (plan §8.1, §14.1 REQ-MC-ANY-001)
cannot answer it from HIR.

The parser does capture the metadata for the DECLARATION-level `@unsafe(...)`
form, but only into module-level `[text]` state that no HIR node references:

```
src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:543  var PENDING_UNSAFE_CAPS: [text] = []
...:552  UNSAFE_ANNOTATIONS.push(decl_name + "|" + PENDING_UNSAFE_REASON + "|" + PENDING_UNSAFE_CAPS.join(","))
```

`/usr/bin/grep -rn UNSAFE_ANNOTATIONS --include=*.spl src/` returns only that file:
the list is written and never read.

The parser also validates nothing — `PENDING_UNSAFE_CAPS.push(par_text_get())`
(line 960) accepts any identifier, so a typo'd capability is silently accepted and
then silently discarded. `src/compiler/00.common/assurance/unsafe_capabilities.spl`
(added 2026-08-21) now provides the canonical table and
`unknown_unsafe_capability_names(caps)` for exactly that validation, but nothing
calls it yet.

## Consequence and current workaround

`any_escape_check(module, profile)` takes the grant as a PROFILE INPUT
(`AnyEscapeProfile.type_erasure_functions`) rather than reading it off the node.
The census driver `src/app/check/any_escape_census.spl` scrapes that grant from
source text. This is stated in both files rather than hidden: only the GRANT is
textual, every finding is still decided on resolved HIR types.

## Fix

1. Add `reason: text` and `capabilities: [UnsafeCapability]` to
   `HirExprKind.UnsafeBlock`, and the same to `HirFunction` for the annotation form.
2. Thread `PENDING_UNSAFE_REASON` / `PENDING_UNSAFE_CAPS` through lowering
   (`20.hir/hir_lowering/_Expressions/expression_core.spl:666`) instead of dropping them.
3. Validate each name through `parse_unsafe_capability` and report
   `unknown_unsafe_capability_names` as a diagnostic.
4. Delete `AnyEscapeProfile.type_erasure_functions` and
   `granted_type_erasure_functions` once (1)-(3) land.
