# MIR transform enum provenance

Source: `test/02_integration/compiler/mir_transform_enum_provenance_spec.spl`.

An enum declaration record with distinct owner/source IDs, runtime identity and
variant provenance survives enabled AOP reconstruction, enabled debug tracing,
SIMD lowering and automatic vectorization. Empty function maps still exercise
module reconstruction; no advice execution is claimed.

Status: authored, full pass integration UNRUN. Separate native probes compile
all eight exact production constructor expressions against 183 actual type
records and verify retained fields, empty defaults, and reproduced old loss.
