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

## Reject unsupported receiver adaptation without erasing metadata

1. Parse a method whose body evaluates `self.base + 1`.
2. Confirm that both facet AST and facet HIR retain the original body.
3. Reject executable-source projection with typed diagnostic `E-AF005` because
   no production receiver adaptation ABI exists yet.
4. Do not replace the body with a placeholder, fake vtable, or source-text
   runtime assertion.

## Keep interfaces declaration-only

1. Parse an interface method that incorrectly supplies a body.
2. Reject it with `E-AF005` and the declaration-only diagnostic.

The executable scenario is intentionally receiver-independent. The canonical
factory ABI remains `<implementation>__facet_witness`; constructing that
factory and adapting `self.base` are separate residual work.
