# `container[key].push(x)` silently loses the write for dict values and tuple/struct fields
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Engine matrix (probed 2026-07-31, later the same day)

The loss is **not uniform across engines or statement scope**:

| Context | `bin/simple run` JIT / interp-mode / native | `bin/simple test` runner |
|---|---|---|
| top-level statements | tuple-field and dict-index **lost** (all engines) | n/a |
| inside a `fn` | **all four shapes work** | tuple-field and dict-index **lost** |

Evidence: a four-shape probe run top-level and `fn main()`-wrapped under JIT
default, `SIMPLE_JIT_STRICT=1`, `SIMPLE_EXECUTION_MODE=interp`, and a
`compile --native` binary (all four shapes correct in-function on all of them);
versus the `group_by` spec, which lost in-function tuple-field pushes under
`bin/simple test` until the fix. The deployed binary at probe time was the
seed banner build, so the `run` columns characterize the seed's engines.

Consequence: this is an **engine divergence**, not a settled language semantic.
The write-back form is correct under both semantics (if indexing yields a
reference, the write-back is a redundant self-assignment), which is why the six
`src/lib` fixes are safe regardless of which behaviour is declared intended.

## Follow-up scan: src/app, src/compiler, test (2026-07-31)

11 further sites with the losing shape, all dict-value receivers. Semantics
settled by `doc/04_architecture/adr/ADR-004-indexed-access-value-semantics.md`
(value semantics; write-back is the contract), after which all 11 were
converted to write-back. Sites:
`src/app/interpreter/module/evaluator.spl:387,423` (note: that tree is
spec-unexercisable), `src/app/diagram/main.spl:130,167`,
`src/compiler/35.semantics/lint/duplicate_typed_args.spl:84,124` (if the loss
applies on its engine, that lint can never see a duplicate),
`src/compiler/99.loader/settlement/linker.spl:142`,
`src/compiler/40.mono/monomorphize/cycle_detector.spl:91,222,281` (cycle
detection would under-report), `src/compiler/90.tools/coupling/gap_matcher.spl:121`.
`test/` has 0 broken sites. The lint for the pattern remains open (ADR-004
consequences).

## Caveats

- Semantics settled 2026-07-31 by ADR-004: value semantics; write-back is the
  only guaranteed mutation form for dict values and indexed tuple/struct
  fields. The lint for the losing pattern is still open — a silently discarded
  mutation is not something the reader can see.

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


## Re-measurement 2026-09-18 — the audit table is stale; one shape is fixed, one is a LANE SPLIT

Binaries: a seed built from `origin/main` `c8fa65bf714` today (51,645,288 B,
sha256 `308de6af84db5c26e2c0`) and, for contrast, the binary deployed at
`bin/simple` (built 2026-09-06).

Same four shapes as the original table, both lanes, fresh seed:

| shape | example | interpret | JIT |
|---|---|---|---|
| array of arrays | `b[0].push(x)` | keeps | keeps |
| **dict value** | `c["k"].push(x)` | **keeps** | keeps |
| write-back | `d["k"] = d["k"].push(x)` | keeps | keeps |
| **tuple field** | `a[0].1.push(x)` | **LOSES** | **keeps** |

Three corrections to the record above:

1. **The dict-value shape is fixed.** It lost the write when this was filed and
   keeps it now. Four of the seven "broken" sites in the audit table were
   dict-value sites, so they are no longer broken by this defect.
2. **The tuple-field shape is now a LANE SPLIT, not a flat failure.** The
   interpret lane still discards the write; the JIT lane keeps it. The original
   entry says "JIT/native unverified" — it is verified now, and the two engines
   disagree, which is the part that still needs an owner.
3. **Both non-dict sites the table lists are already remediated in-tree**, so no
   live stdlib site is known to lose a write today:
   - `gc_async_mut/pure/collections.spl` keeps two parallel arrays
     (`keys: [K]`, `members: [[T]]`) precisely to avoid the tuple-field shape,
     and says so in a comment.
   - `common/encoding/font_cldr_rank.spl` uses the read-modify-write form with a
     comment citing this bug id.

**Anyone re-running this must check their binary first.** On the deployed
2026-09-06 seed the dict-value shape still fails, so measuring with it reproduces
the original table and would lead to "fixing" code that is already correct. That
binary carries a separate defect
(`seed_jit_optional_unwrap_returns_enum_box_2026-09-18.md`);
`scripts/check/check-deployed-binary-optional-unwrap.shs` tells the two apart in
about a second.

Pinned by `test/01_unit/interpreter/mutate_through_index_shapes_spec.spl`
(7 examples): the three working shapes are now guarded, since the dict-value one
is recently-fixed behaviour with production callers and nothing else covered it.
The tuple-field shape is deliberately left unasserted there — asserting either
lane's answer would add a red or bless a defect — so it remains this record's one
live item. Measured: 7/7 on the fresh seed; the three dict examples fail on the
deployed seed.
