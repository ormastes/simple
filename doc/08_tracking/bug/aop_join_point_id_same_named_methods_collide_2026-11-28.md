# Forward join-point ids collide for same-named methods of different types

**Found:** 2026-11-28, review of aspect plan stage AW-2 (seed `simple-local-20261128f`).
**Status:** open. **Must be fixed before the `join-point|` writer is wired into
TLDR publication** (plan stage AW-1w).

## Reproduction

```simple
struct P:
    a: i64

struct Q:
    a: i64

fn target(n: i64) -> i64:
    n

impl P:
    fn view(n: i64) -> i64:
        target(n)

impl Q:
    fn view(n: i64) -> i64:
        target(n)
```

Lowered as module `x`, the module has two `HirFunction`s named `view`
(both `is_method`). Observed:

| Path | Result |
|------|--------|
| `aop_directory_facts_from_hir_v1` (production today) | two facts with the same id `x::view` |
| `join_point_tldr_entry_v2` (AW-2 writer) | `Err("join-point-duplicate")` |

## Defects

1. **HIR path emits duplicate ids.** `aop_match_cache_driver_v1.spl` builds the
   id as `"{module_key}::{jp.source_symbol}"` and `ForwardJoinPoint.source_symbol`
   is the bare function name. Two join points share one `JoinPointId`, so a
   shard, an owner map or a weave key cannot tell them apart, and
   `canonical_identity_text_lt` ordering in `directory_join_point_table_v3.spl`
   rejects the table (ids must be strictly increasing).
2. **The AW-2 writer's name lookup is last-wins.**
   `aspect_tldr_section_writer_v1.spl` maps function name -> index before it
   reads the signature and body digest of each join point. With two `view`
   functions both rows would carry the digests of the second one. Today this
   cannot reach a section, because the builder then refuses the duplicate id;
   it would become a wrong-digest defect the moment ids are qualified without
   also fixing the lookup.

The section builder's refusal is the correct behaviour for an ambiguous id and
is covered by "two rows of one symbol are refused" in
`test/01_unit/compiler/aop/join_point_section_v2_spec.spl`. The cost is that a
module with such methods publishes no `join-point|` section, so its directory
facts are incomplete (a miss), never wrong.

## Fix direction

Qualify the join-point symbol with its owner type (for example `x::P.view`) in
`forward_join_points_for_module_v1`, use the same qualified symbol in the HIR
facts path and in the writer, and look the function up by its `SymbolId`
instead of its name. Selectors that name a bare method then need a stated
matching rule (bare name matches every owner, or must be qualified).
