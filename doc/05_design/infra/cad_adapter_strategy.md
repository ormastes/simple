# CAD Adapter Strategy

`cad{}` starts as a typed pure Simple authoring model, not a full geometry
kernel. The first stable interchange target is a representative STEP AP242
fixture exporter over recorded primitives, features, parameters, assemblies, and
constraints.

OpenSCAD and CadQuery adapters should be added only after the typed IR has a
stable topology boundary. Until then, adapters must be generated from the IR as
lossy fixture/export tools and must not become the source of truth for Simple CAD
semantics.

Adapter responsibilities:

- OpenSCAD: preview-oriented constructive solid geometry for boxes, cylinders,
  holes, fillets where representable, and parameter substitution.
- CadQuery: richer Python-side prototyping for fixture comparison and eventual
  BREP handoff experiments.
- STEP AP242: industrial exchange fixture output and future conformance gate.

Rejected for this slice:

- embedding OpenSCAD/CadQuery syntax directly in `cad{}` payloads
- claiming topology/PMI completeness without a kernel design
- validating against external STEP toolchains in unit tests
