<!-- codex-impl -->
# World Units and Newunit Architecture

`newunit` is a nominal wrapper declaration that lowers to the existing standalone unit/custom-primitive path. It is intentionally separate from measurement `unit` families and derived expressions so IDs, handles, flags, and ABI tags do not enter metrology catalogs.

The units catalog is SDN-backed data under `src/lib/common/units/catalog/`. Runtime/compiler semantics stay in code under `src/lib/common/units/model/` and the existing parser/interpreter/type-checking layers. Catalog data is local and versioned; importers may refresh it, but request/compiler hot paths read committed normalized catalogs only.

SFFI continues to resolve named wrappers through the shared custom primitive registry. A `newunit` is ABI-transparent only when the backing type resolves to a supported C-compatible primitive. Unsupported wrappers are rejected by SFFI lint before generation.

Public primitive API lint treats `newunit`, measurement `unit`, enums, Option, and Result as semantic public API types. Raw primitives remain allowed only at explicitly annotated ABI or math boundaries.
