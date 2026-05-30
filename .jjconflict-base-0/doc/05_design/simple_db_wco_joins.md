# Simple DB WCO Join Decision

- **Feature request:** FR-SIMPLE-DB-0005
- **Decision:** defer implementation until relational join prerequisites exist
- **Research:** `doc/01_research/local/simple_db_wco_joins_2026-05-29.md`

## Boundary

The current Simple DB planner may keep its symbolic `Join` plan node for future
cost-model experiments, but no execution path should claim WCO join support
until the engine has:

- a multi-relation query model,
- sorted keyset iterators,
- multi-attribute index layout,
- join workload fixtures,
- benchmark evidence against the existing nested/scan plan.

## Near-Term Replacement

Use the already-landed posting-list bitmap primitives for repeated token
conjunction/disjunction. They solve the current text-search workload without
introducing the storage complexity required by Leapfrog/NPRR-style joins.

## Reopen Trigger

Reopen design only when at least one tracked workload has a cyclic or high-fanout
join query where binary/nested plans produce large intermediate results.
