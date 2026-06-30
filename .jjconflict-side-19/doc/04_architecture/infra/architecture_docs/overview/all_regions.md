<!-- codex-design -->
# All Regions Architecture

Filed: 2026-04-22

## Architecture

Use a layered model instead of making SDN the universal authoring language.

1. Core Simple: computation, modules, typing, macros, verification, compilation.
2. `schema{}`: contracts for validation, versions, units, identities, field IDs, defaults, compatibility, and canonical serialization.
3. Domain blocks: `style{}`, `ui{}`, `music{}`, `bim{}`, `cad{}`, `city{}`, `rtl{}`.
4. SDN: instances, manifests, metadata, normalized snapshots, generated IR, caches, and tool interchange.

## Compiler Shape

The first compiler layer should be a generic raw top-level domain-block carrier:

- contextual recognition of approved block names followed by `{`;
- raw payload capture with source spans;
- AST/outline visibility;
- metadata-only HIR lowering until a domain has real semantics;
- domain-specific semantic passes added later behind feature requests.

This matches existing custom-block and `lean{}` precedent while avoiding premature commitment to CAD kernels, CSS layout engines, or IFC/STEP/MusicXML exporters.

## MDSOC Boundaries

Each domain is a virtual capsule. Shared concerns are cross-cutting transforms: raw capture, diagnostics, outline/LSP, schema binding, import/export conformance, and generated SDN metadata.

