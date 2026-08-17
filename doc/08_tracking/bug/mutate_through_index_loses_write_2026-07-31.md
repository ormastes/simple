# `container[key].push(x)` silently loses the write for dict values and tuple/struct fields

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Date:** 2026-07-31
**Engine tested:** tree-walk interpreter (`bin/simple test`) — JIT/native unverified
**Severity:** silent wrong results, no error or warning

## RE-ATTRIBUTION + NARROWED RULE (2026-08-17)

Two corrections, both measured today under `bin/simple` (Rust seed, mtime
2026-08-16 22:59) by running one program under both engines.

**1. The JIT is now verified, and it is CORRECT.** The "JIT/native unverified"
note above is resolved: every shape in the table below persists the write under
`SIMPLE_EXECUTION_MODE=jit` and only the tree-walk **interpreter** loses it. So
this is an interpreter defect. It was triaged into the `src/compiler/50.mir/**`
lane against `_MirLoweringExpr/method_calls_literals.spl`; that is the wrong
owner — MIR lowering feeds the engine that already behaves.

**2. "Indexing a dict yields a copy" is too broad.** Sweeping the class as a
container x element MATRIX (rather than the four filed anecdotes) shows the
discriminator is narrower than the container kind. Interpreter results:

| shape | result |
|---|---|
| `Dict<text, [i64]>` — `c["k"].push(x)` | **write lost** |
| `Dict<i64, [text]>` — `c[7].push(x)` | persists |
| `[(i64, [i64])]` — `a[0].1.push(x)` | **write lost** |
| `[Bag]` where `Bag.items: [i64]` — `b[0].items.push(x)` | persists |
| `Dict<text, Bag>` — `d["g"].items.push(x)` | persists |
| `[[i64]]` / `[[[i64]]]` | persists |
| explicit write-back `d[k] = d[k].push(x)` | persists |

So the filed claim that **struct** fields lose the write does not reproduce —
both struct-field shapes persist — and dict behaviour depends on the key/element
types, not on it being a dict. Whoever fixes this should treat the matrix, not
the container kind, as the specification.

Specs (RED today):
- reproducing: `test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl`
- prevention (the matrix above): `test/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.spl`

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
