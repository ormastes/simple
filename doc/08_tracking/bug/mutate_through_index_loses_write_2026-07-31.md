# `container[key].push(x)` silently loses the write for dict values and tuple/struct fields

**Date:** 2026-07-31
**Engine tested:** tree-walk interpreter (`bin/simple test`) — JIT/native unverified
**Severity:** silent wrong results, no error or warning

## The rule

Not "arrays are value types" — that is too broad and predicts failures that do
not happen. Probed four shapes directly:

| Shape | Example | Result |
|---|---|---|
| through a tuple field | `a[0].1.push(x)` where `a: [(i64, [i64])]` | **write lost** |
| array of arrays | `b[0].push(x)` where `b: [[i64]]` | works |
| through a dict value | `c["k"].push(x)` where `c: Dict<text, [i64]>` | **write lost** |
| write-back | `d["k"] = d["k"].push(x)` | works |

So indexing an array to reach a **nested array** gives a mutable reference, but
indexing to reach a **tuple/struct field**, or indexing a **dict**, yields a copy.
The push mutates the copy and it is discarded.

## Audited sites

31 mutate-through-index sites in `src/lib`. Classified by receiver type:

### Broken (6, plus one probable)

| Site | Receiver | Shape |
|---|---|---|
| `gc_async_mut/pure/collections.spl:91` | `[(K, [T])]` | tuple field |
| `nogc_sync_mut/src/db.spl:203` | `Dict<text, [[text]]>` | dict value |
| `nogc_sync_mut/dependency_tracker/graph.spl:54` | `Dict<text, [text]>` | dict value |
| `nogc_sync_mut/src/exp/run.spl:103` | `Dict<text, [MetricEntry]>` | dict value |
| `nogc_sync_mut/src/exp/query.spl:125` | `Dict<text, [MetricPoint]>` | dict value |
| `common/encoding/font_cldr_rank.spl:544` | `[CldrLanguageTotal]` | struct field |
| `nogc_sync_mut/src/exp/run.spl:250` | same pattern as :103 | probable |

`graph.spl:54` is the one worth looking at first: `self.edges[from].push(to)` on
a dependency graph means **every node keeps only its first edge**. Anything
built on that traversal is wrong in a way that looks like a sparse graph rather
than like a bug.

### Not broken (the rest)

- `nogc_sync_mut/src/table.spl:459,636,655,674` — all use the write-back form
  `x[k] = x[k].push(v)`.
- `common/search/multi.spl:128,129` — `tchild_bytes: [[i64]]`, array of arrays.
- `gpu/browser_engine/…paint_layout.spl:2148,2150,2153,2368-2371` —
  `members: [[i32]]`, `child_contexts: [[i32]]`,
  `scrollbar_commands_at: [[DrawIrCommand]]`, all array of arrays.

## Fix shape

Write-back is correct everywhere and is already the idiom `table.spl` uses:

```
var bucket = c[k]
bucket.push(x)
c[k] = bucket
```

It copies the bucket per insert, so a hot loop over one key degrades to O(n²).
Acceptable for the graph/metrics sites (small buckets, cold paths); not
acceptable as the `group_by` fix, which is why that one is still open — see
`group_by_drops_all_but_first_member_2026-07-31.md`.

## Caveats

- **Interpreter only.** `bin/simple test` runs the tree-walk interpreter; the JIT
  and native backends are not covered and may differ in either direction. The
  probe should be re-run under `SIMPLE_EXECUTION_MODE=jit` and native before any
  of these are called correct-or-broken on those engines.
- The audit is `src/lib` only. `src/app`, `src/compiler` and `test` were not
  scanned; the same grep applies.
- Whether this is intended semantics or a defect is not settled here. If
  intended, it needs a lint — a silently discarded mutation is not something the
  reader can see.

## Reproducer

```
var c: Dict<text, [i64]> = {}
c["k"] = [1]
c["k"].push(2)
# c["k"].len() is 1
```

## Related

- `.claude/memory/feedback_arrays_value_types.md` — refine: the copy happens at
  dict-value and tuple/struct-field access, not at every array index
- `doc/07_guide/language/dict_native_pitfalls.md`
