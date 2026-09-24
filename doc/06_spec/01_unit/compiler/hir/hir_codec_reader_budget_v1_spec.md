# hir codec reader budget v1

Authored scenario companion for `test/01_unit/compiler/hir/hir_codec_reader_budget_v1_spec.spl`. Requirement: REQ-CSM-024.

These scenarios call the bounded codec or graph owner with typed inputs. They
check canonical ordering, attempted work and refusal boundaries as named below.
No branch percentage, golden-byte admission or allocator/RSS evidence is claimed.
Execution and generated-manual qualification await the admitted self-hosted runtime.

## Scenarios

- should decode canonical scalar lines within exact limits
- should preserve empty and escaped text values at the edge
- should accept exact input, allocation, and work limits at equality
- should reject one-short input, allocation, node, depth, or work limits
- should poison the cursor on malformed integer and truncation
- should bind executed reader outcomes to the admitted build
