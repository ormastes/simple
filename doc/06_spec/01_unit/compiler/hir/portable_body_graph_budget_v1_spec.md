# portable body graph budget v1

Authored scenario companion for `test/01_unit/compiler/hir/portable_body_graph_budget_v1_spec.spl`. Requirement: REQ-CSM-024.

These scenarios call the bounded codec or graph owner with typed inputs. They
check canonical ordering, attempted work and refusal boundaries as named below.
No branch percentage, golden-byte admission or allocator/RSS evidence is claimed.
Execution and generated-manual qualification await the admitted self-hosted runtime.

## Scenarios

- should analyze a deduplicated DAG with deterministic longest path
- should preserve empty, fanout, and duplicate-occurrence edge cases
- should make reverse occurrence order stable and semantic mutation visible
- should reject foreign and recursive graph semantics before a digest grant
- should reject one-short graph and precharge budgets
- should refuse one-short text, work, and retained budgets without growing a poisoned ledger
- should bind graph budget hits to the admitted build
