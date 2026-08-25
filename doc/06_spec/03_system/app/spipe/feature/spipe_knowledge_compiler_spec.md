# SPipe Knowledge Compiler Primary Workflow — Authored Design Scaffold

> **Not generated and not PASS evidence.** The executable scaffold is
> deliberately fail-fast until production oracles exist.

**Source:** `test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl`  
**Generation command:** `bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl --output doc/06_spec --no-index`

## REQ/NFR map

| Flow | Requirements | NFRs |
|---|---|---|
| Index canonical knowledge artifacts | REQ-SPKC-001..005, 017..018, 028..029 | NFR-SPKC-001..002, 009..010, 023 |
| Browse virtual knowledge views | REQ-SPKC-006..009, 026, 030 | NFR-SPKC-003..005, 011, 019 |
| Search and trace artifacts | REQ-SPKC-017..018 | NFR-SPKC-001..002 |
| Apply a transactional refactor | REQ-SPKC-019..020, 029 | NFR-SPKC-008..010 |
| Audit tree balance and promotion candidates | REQ-SPKC-021..025 | NFR-SPKC-017..018, 024 |
| Compatibility/evidence | REQ-SPKC-027..030 | NFR-SPKC-020..022, 025 |

## Operator flow

1. Index canonical knowledge artifacts.
2. Browse virtual knowledge views.
3. Search and trace artifacts.
4. Apply a transactional refactor.
5. Audit tree balance and promotion candidates.

## Expected evidence

The completed manual must show immutable snapshot/UID results, bounded virtual
views, explained search and trace authority, an exact transaction recovery
receipt, and review-only rebalance/promotion proposals. The frozen setup and
checker helpers must execute production owners and remain present in folded
source. Until then every helper raises `DESIGN-SCAFFOLD` and the result is RED.

## Recovery and limitations

Do not replace fail-fast helpers with source inspection or placeholder passes.
Keep standalone, linked-project, and two-worktree fixtures isolated. Optional
providers and deferred FUSE/ProjFS cannot satisfy unavailable evidence.
