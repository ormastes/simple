# hir codec key order v1

Authored scenario companion for `test/01_unit/compiler/hir/hir_codec_key_order_v1_spec.spl`. Requirement: REQ-CSM-024.

These scenarios call the bounded codec or graph owner with typed inputs. They
check canonical ordering, attempted work and refusal boundaries as named below.
No branch percentage, golden-byte admission or allocator/RSS evidence is claimed.
Execution and generated-manual qualification await the admitted self-hosted runtime.

## Scenarios

- should order signed integer keys without changing equal-key order
- should order symbol and UTF-8 text keys by their typed contract
- should preserve reverse odd merge runs and equal-key stability
- should preserve nil-before-present and singleton edge ordering
- should keep opposite typed-module insertion orders byte-identical after admission
- should bind executed ordering hits to the admitted build
