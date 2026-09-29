<!-- codex-research -->
# Typed facet local research

## Current substrate

`src/lib/common/aspect_pack.spl` and `src/compiler/99.loader/module_loader_compat.spl`
already provide validated byte-pack admission, indexed key lookup, generations,
pin/unpin, catalog replacement guards, and a loader lifecycle gate.  This is
untyped `facet_key: text` machinery; it is not a language `FacetRef<T>`.

The compiler has no `aspect`/`facet` tokens, typed AST/HIR/MIR nodes, witness
ABI, or runtime dispatch.  Existing `facet_syntax.spl` and `facet_registry.spl`
are standalone test/library models and are not compiler authority.  Ordinary
receiver method parsing accepts `obj.method(` immediately, while
`ExprKind.MethodCall` and `HirExprKind.MethodCall` have no type-argument field;
therefore `obj.facet<T>()` requires a dedicated representation or a compatible
method-call schema extension.

## Safety boundary

`ModuleFacetRefV1.release` currently reaches payload-only `apk_facet_unpin_v1`.
There is no exact mapper receipt, final-unpin lease, or mapper-owner release
port.  Executable mapping release must therefore remain unavailable until a
loader-owned, generation-bound V2 lifecycle bridge exists.  Legacy raw/bulk
mapper operations must not bypass a receipt-bearing binding.

## Consequence

A first language slice must introduce a dedicated typed acquisition expression
and contract metadata, not rebrand the test helper or expose loader addresses.
Current selected-requirement status must be established separately; no existing
document reviewed here authorizes this grammar, public ABI, or executable unload
behavior.
