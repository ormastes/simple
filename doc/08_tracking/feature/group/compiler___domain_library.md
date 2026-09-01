# compiler_+_domain_library

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-008"></a>FR-COMPILER-008 | Add music{} authoring with MusicXML interchange | Add a `music{}` authoring surface for scores, staves, measures, voices, rhythm, pitch, articulations, and metadata, with MusicXML as the first interchange target and MEI/LilyPond/ABC adapters deferred until the core model is stable. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/02_requirements/feature/all_regions.md](../../../02_requirements/feature/all_regions.md#feature-FR-COMPILER-008) |
| <a id="feature-FR-COMPILER-009"></a>FR-COMPILER-009 | Add bim{} and city{} standards bindings | Add BIM and city-scale authoring surfaces that bind authored objects to IFC, bSDD, gbXML, and CityGML identities/properties before attempting deep geometry or simulation semantics. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/02_requirements/feature/all_regions.md](../../../02_requirements/feature/all_regions.md#feature-FR-COMPILER-009) |
