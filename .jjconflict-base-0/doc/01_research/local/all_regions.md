<!-- codex-research -->
# All Regions Local Research

Filed: 2026-04-22

## Findings

- SDN is already a separate data/config surface, not the universal authoring grammar. See `doc/04_architecture/parser_file_locations_2026-02-04.md` and SDN parser ownership under `src/lib/std/sdn/`.
- Existing dedicated surfaces already prove the layered model: math blocks (`m{}`, `loss{}`, `nograd{}`), Lean verification, SQP query/persistence, UI contracts/theme CSS generation, and a bounded Simple-to-VHDL-2008 backend.
- No first-class `schema{}`, `style{}`, `music{}`, `bim{}`, `cad{}`, or `city{}` top-level authoring surfaces were found.
- Parser extension points exist, but full top-level domain blocks touch several layers: Simple parser declarations, fixed AST declaration tags, Rust parser custom-block handling, Tree-sitter outline, HIR/lowering, docs, and tests.
- Rust parser has expression-level raw custom blocks via `TokenKind::CustomBlock`; `lean{}` is the best precedent for raw capture plus semantic lowering.
- UI has shared protocol/theme/browser surfaces, but no authoring DSL for layout/cascade semantics.
- RTL has a real backend path already; future work should harden subset boundaries and optional SystemVerilog interop rather than forcing RTL through SDN.

## Gaps

- General schema/contracts are missing outside narrow MCP and SQP-specific schema concepts.
- Domain-specific interchange targets are not represented in docs or source for MusicXML, MEI, IFC, bSDD, gbXML, CityGML, STEP AP242, OpenSCAD, or CadQuery.
- A one-pass "all regions" implementation is not credible; the correct near-term implementation is a staged domain-block architecture with feature requests for semantic depth.

