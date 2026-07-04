# Simple DB Worst-Case-Optimal Join Research

- **Feature request:** FR-SIMPLE-DB-0005
- **Date:** 2026-05-29
- **Status:** explicit deferral / no implementation now

## Current State

Simple DB has scan, prefix, text, BRIN-style summary, learned static-segment,
learned cardinality, and posting-list bitmap primitives. The planner contains a
symbolic `PlanNodeKind.Join` candidate for `AND` predicates, but there is no
relational join executor, join key schema, multi-table catalog, or sorted
multi-attribute index surface.

The current hot workloads are:

| workload | current path | WCO fit |
| --- | --- | --- |
| key/value exact and prefix lookup | prefix/text indexes | no; unary lookup |
| DBFS parent/name namespace lookup | parent/name prefix index | no; point/prefix lookup |
| SDN filter chains | row scan or per-field prefix index | weak; conjunctive filters over one table |
| text token AND/OR | posting-list bitmap intersection/union | partial; set intersection is enough |
| BRIN refine | coarse range filter plus exact scan | no; unary range refine |

## WCO Join Applicability

Worst-case-optimal joins are useful for cyclic or high-fanout multiway joins
where binary join plans can materialize large intermediates. Representative
examples are triangle queries and multi-hop graph patterns:

```text
R(a,b) join S(b,c) join T(a,c)
edge(src,mid) join edge(mid,dst) join label(dst,x)
```

Simple DB does not yet expose this shape. Its current query API is mostly
single-table filtering and lookup. The existing text posting-list path already
uses bitmap intersection for token conjunctions, which is the right simpler
operator until query shapes become true multi-relation joins.

## Storage/Layout Prerequisites

Before a WCO executor is justified, Simple DB needs:

1. A relation/catalog layer with typed join-key columns and stable row IDs.
2. Sorted adjacency or trie-like indexes keyed by ordered attribute prefixes.
3. Iterator APIs for seek, next, and leapfrog-style intersection over sorted
   keys.
4. Cardinality/selectivity feedback for multi-attribute predicates.
5. Workload fixtures that demonstrate cyclic or high-fanout joins where binary
   plans materialize avoidable intermediates.

## Decision

Do not implement WCO joins in the current Phase 1/2 Simple DB engine. Keep using
posting-list bitmaps for token conjunction and prefix/BRIN/learned indexes for
unary lookups. Revisit WCO joins only after the planner grows a real relational
join executor and the storage layer exposes sorted multi-attribute keyset
indexes.

This is a scoped rejection for now, not a permanent rejection of the technique.
