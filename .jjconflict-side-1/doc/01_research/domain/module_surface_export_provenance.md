<!-- codex-research -->
# Module Surface Export Provenance — Domain Research

## Official findings

Rust treats a public `use` as a re-exported name and explicitly allows that path
to provide public access distinct from the declaration's namespace path. This
supports representing exported name and declaration origin separately rather
than copying declarations into facade modules. See the
[Rust Reference: visibility and re-exporting](https://doc.rust-lang.org/reference/visibility-and-privacy.html#re-exporting-and-visibility)
and [use declarations](https://doc.rust-lang.org/reference/items/use-declarations.html#use-visibility).

Clang module maps model exports as semantic module relationships: an export
declaration identifies imported modules automatically re-exported through the
enclosing API, while wildcard exports expand imported module APIs. Clang also
distinguishes logical module identity from physical headers and treats paths
resolving to the same file as the same header identity. See
[Clang Modules: export declarations and module maps](https://clang.llvm.org/docs/Modules.html#export-declaration).

Clang's standard C++ module documentation distinguishes module interface units
from implementation units and uses built module interfaces as importable
artifacts. This reinforces building a stable declaration/export surface before
consumer lowering rather than discovering exports ad hoc in each consumer. See
[Clang Standard C++ Modules](https://clang.llvm.org/docs/StandardCPlusPlusModules.html#background-and-terminology).

## Applied principles

1. Separate public spelling from canonical declaration identity.
2. Resolve export edges once at the module-interface boundary.
3. Preserve physical identity through logical aliases.
4. Detect ambiguous owners and cycles deterministically.
5. Cache semantic export results, not repeated textual traversal.
6. Keep future body reachability separate from the immediate declaration
   provenance slice.

## Non-goals

This work does not adopt another language's visibility rules, serialize a new
module format, or immediately replace entry-closure discovery. The references
provide architectural precedent for explicit semantic export graphs.
