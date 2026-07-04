<!-- codex-research -->
# All Regions Domain Research

Filed: 2026-04-22

## Standards Anchors

- Schema/contracts: JSON Schema 2020-12 for JSON-like validation (`https://json-schema.org/specification`); Protocol Buffers for field numbers, generated APIs, and wire-safe evolution (`https://protobuf.dev/programming-guides/editions/`).
- UI/style: WHATWG HTML living standard (`https://html.spec.whatwg.org/multipage/`) and W3C CSS modules for display, flex, grid, cascade, and layout semantics.
- Music: MusicXML 4.0 for notation interchange (`https://www.w3.org/2021/06/musicxml40/`), MEI for scholarly encoding, LilyPond for engraving-oriented authoring, ABC for compact notation.
- BIM/AEC/city: IFC schema specifications and IFC 4.3 / ISO 16739-1:2024 from buildingSMART, bSDD for dictionaries, gbXML for energy exchange, CityGML 3.0 for city-scale 3D models.
- CAD/manufacturing: STEP AP242 / ISO 10303-242:2025 for managed model-based 3D engineering, with OpenSCAD and CadQuery as authoring precedents.
- RTL/hardware: IEEE 1076-2019 VHDL and IEEE 1800-2023 SystemVerilog remain the interoperability anchors.

## Conclusion

SDN should dominate tree-like data, manifests, metadata, snapshots, catalogs, and generated interchange. Domains whose meaning depends on layout/cascade, topology/geometry, notation/time, or industry schemas need dedicated authoring blocks with SDN as a carrier, not as the primary language.

