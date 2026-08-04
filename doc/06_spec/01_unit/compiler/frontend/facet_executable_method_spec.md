# Executable facet method projection

This manual specifies the first real frontend-to-MIR slice for facet method
bodies. It does not claim that a facet witness factory or runtime receiver ABI
exists.

## Preserve and lower a receiver-independent body

1. Parse a declaration-only `Debuggable.debug_name` interface method.
2. Parse `ConstantDebug.debug_name` with the executable body `"constant"`.
3. Retain that body unchanged in both `FacetMethodDecl.body_source` and
   `HirFacetMethod.body_source`.
4. Derive the canonical symbol
   `ConstantDebug__facet_witness__debug_name`.
5. Project an ordinary top-level Simple function with an explicit typed base
   parameter and the retained body.
6. Confirm that the authoritative frontend, HIR lowering, and MIR lowering all
   contain the canonical function.

## Adapt `self.base` through the explicit receiver ABI

1. Parse a method whose body evaluates `self.base + 1`.
2. Confirm that both facet AST and facet HIR retain the original body.
3. Project an ordinary function whose first parameter is the concrete base
   value and rewrite the receiver token to that parameter.
4. Confirm that the receiver-aware function reaches ordinary HIR and MIR.
5. Do not replace the body with a placeholder, fake vtable, or source-text
   runtime assertion.

String literals and comments are not rewritten. Bare `self` remains a typed
`E-AF005` failure because the value semantics of a facet wrapper have not been
defined; its original body remains available in facet metadata.

## Keep interfaces declaration-only

1. Parse an interface method that incorrectly supplies a body.
2. Reject it with `E-AF005` and the declaration-only diagnostic.

The witness-method ABI passes the concrete base as argument zero. The canonical
factory ABI remains `<implementation>__facet_witness`; constructing and
publishing that factory and its relocation-aware method table remain separate
residual work.
