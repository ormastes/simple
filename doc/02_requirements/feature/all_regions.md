<!-- codex-research -->
# All Regions Feature Requirements

Filed: 2026-04-22

## Selected Direction

Implement Simple "all regions" support as a layered language family:

- Simple core remains responsible for computation, typing, macros, verification, and compilation.
- `schema{}` becomes the cross-domain contract layer for constraints, versioning, validation, units, identities, and compatibility.
- Dedicated domain blocks cover authoring surfaces where SDN is semantically too weak: `style{}` / `ui{}`, `music{}`, `bim{}`, `cad{}`, `city{}`, and `rtl{}`.
- SDN remains the carrier for instances, manifests, metadata, generated IR, caches, tables, and tool interchange.

## Requirements

- REQ-001: Document the region map and define which domains are SDN-primary, schema-backed, or dedicated-DSL authoring surfaces.
- REQ-002: Add a compiler-facing feature-request path for top-level raw domain blocks.
- REQ-003: Prioritize `schema{}` first, then `style{}` / `ui{}`, then RTL hardening, then music, BIM/city, and CAD.
- REQ-004: Each dedicated domain block must name its primary external interchange standard before implementation.
- REQ-005: Domain block implementation must start with raw capture, AST/outline visibility, and diagnostics before deep semantics.
- REQ-006: Deep semantics for music, BIM, CAD, and city/geospatial must be separate feature requests unless they can be completed and verified in the current implementation window.

