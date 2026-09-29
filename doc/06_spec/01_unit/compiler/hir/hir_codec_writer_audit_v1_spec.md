# hir codec writer audit v1

Authored scenario companion for `test/01_unit/compiler/hir/hir_codec_writer_audit_v1_spec.spl`. Requirement: REQ-CSM-024.

These scenarios call the bounded codec or graph owner with typed inputs. They
check canonical ordering, attempted work and refusal boundaries as named below.
No branch percentage, golden-byte admission or allocator/RSS evidence is claimed.
Execution and generated-manual qualification await the admitted self-hosted runtime.

## Scenarios

- should finish a complete bounded frame with charged output
- should seal full chunks while keeping the mutable part bounded
- should finalize legacy small and 511, 512, and 513 line writers
- should charge exact scalar bounds and refuse every one-short limit
- should preserve a real legacy HIR encode decode reencode
- should refuse before materializing work beyond output and work bounds
- should retain failed writer accounting in the audit observer
- should bind writer audit hits to the admitted build
