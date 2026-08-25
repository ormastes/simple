# SPipe Rebalancing and Promotion — Authored Design Scaffold

> **Not generated and not PASS evidence.** Rebalancer, promotion, and generated
> skill oracles remain deliberately red.

**Source:** `test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl`  
**Generation command:** `bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl --output doc/06_spec --no-index`

## REQ/NFR map

- Rebalancing: REQ-SPKC-021..022; NFR-SPKC-001, 011, 017, 023.
- Promotion: REQ-SPKC-023..024; NFR-SPKC-004, 006..007, 018, 021..022.
- Skills/phases/migration: REQ-SPKC-025, 028..030; NFR-SPKC-002..003, 019..025.

## Operator flow

Audit tree balance and promotion candidates without changing canonical content.
Review connected deterministic clusters, every objective term, constraints,
churn, public paths, proposal approval, provenance, conflicts, license/secret
findings, trust, generalized wording, and consuming-project validation.

## Hostile and failure behavior

Disconnected/budget-exhausted graphs preserve the prior view and return
`budget_exceeded`; hard-constraint conflicts return `constraint_conflict`;
stale or unapproved physical proposals return `unauthorized` or a typed stale
proposal. Prompt injection remains artifact data. Secrets, incompatible
licenses, untrusted scope, insufficient independent-project evidence,
conflicting policy, semantic failure, or consumer failure must prevent
publication. Generated skills with stale hashes must fail freshness checks.

## Evidence limitation

Retain proposal, rollback, provenance, review, and generated-hash artifacts.
The current helpers raise `DESIGN-SCAFFOLD`; no organization, publication, or
generated-surface PASS is claimed.
