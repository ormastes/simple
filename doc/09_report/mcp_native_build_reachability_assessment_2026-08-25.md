# Is a local MCP binary reachable through `native-build`? Measured answer: not soon, and not as a queue (2026-08-25)

- **Status:** ASSESSMENT — no fix here. Written to support a scope decision.
- **Question:** after four compiler defects fixed and one library module
  annotated, how much stands between this host and
  `native-build src/app/mcp/main.spl` producing a working binary?
- **Short answer:** **75 errors across 14 distinct kinds, in the MIR phase
  alone** — and every phase after MIR is still unmeasured because the build has
  never reached one. This is a population of independent feature gaps, not a
  chain of blockers.

## Measured, current `origin/main`, whole 61-module closure

`native-build src/app/mcp/main.spl`, all MIR-phase diagnostics collected:

| count | error kind |
|---|---|
| 27 | `unresolved method call` — **12 distinct methods** |
| 14 | `enum match: unsupported arm pattern` |
| 11 | `unsupported MIR type kind [infer-arm]` |
| 7 | `for-in over non-array iterables` (#143) |
| 11 | `undefined variable` — 7 distinct names (`AssistantTimelineRecord`, `Vec8i`, `AssistantStore`, `Utf8Provider`, `AssistantSessionRecord`, `AssistantChildTaskRecord`, `ASSISTANT_STORE_ROOT`) |
| 3 | `assignment target has no local binding` |
| 2 | `unsupported range index a[start..end]` |
| 1 | `char_code_at receiver is not text` |
| **75** | **total, 14 kinds** |

The 27 unresolved method calls are: `new` x8, `index_of` x4, `upper` x3,
`to_string` x2, `to_int` x2, `splat` x2, and one each of `to_list`, `to_float`,
`supports`, `sort`, `slice`, `chars`.

## Why the earlier "queue" framing understated it

Working inside `text_advanced.spl` produced a queue — untyped params -> range
index -> `chars` -> ... — because a single module surfaces its gaps one at a
time, each hidden behind the last. Across the whole closure that is not the
shape: 14 kinds fail in parallel, in different modules, for unrelated reasons.
Clearing any one of them uncovers nothing; it just removes its rows.

## Patch or project, per class

- **`enum match: unsupported arm pattern` (14)** — a pattern-matching feature in
  MIR lowering. One project, probably covering all 14.
- **`unresolved method call` (27 / 12 methods)** — each needs a native lowering
  and, for most, a runtime helper. `new` x8 may collapse to one
  constructor/static-dispatch fix; the rest look individual. Call it 1 project +
  ~8-10 patches.
- **`infer-arm` (11)** — the untyped-value class this lane already worked twice.
  More annotations where the source omits types, real inference where it does
  not. Patches, possibly many.
- **`#143` (7) + range index (2)** — two NAMED work items already recorded:
  implement `lower_range` in index position, and an array-slice runtime helper.
  Both projects, both deliberately loud today
  (`slice_index_range_form_unimplemented_and_misnamed_2026-08-25.md`).
- **`undefined variable` (11 / 7 names)** — resolution failures on specific
  types and one global. Plausibly one root cause; unmeasured.
- **`assignment target has no local binding` (3)**, **`char_code_at receiver is
  not text` (1)** — small, unclassified.

Roughly **6-8 independent work items, of which 3-4 are projects**, to clear the
MIR phase alone.

## And the MIR phase is not the finish line

Everything after it is unmeasured because the build has never got there:

1. **Borrow check.** `borrow_check()` runs AFTER `lower_to_mir`
   (`80.driver/driver_aot_pipeline.spl`), so the NLL false positive in
   `nll_mut_borrow_of_local_false_positive_at_return_2026-08-24.md` **has never
   executed on this closure**. `LivenessAnalysis.record_use`/`record_def` have
   no callers anywhere in the tree, so the analysis has never run on anything —
   expect its first execution to surface a BACKLOG, not a single failure, and do
   not read a large initial count as a regression from whatever lands just
   before it.
2. **Codegen, link, and execution.** Never reached. A binary that exists is not
   a binary that works; the MCP server must still answer a real JSON-RPC
   `initialize`.

## Recommendation

Treat "local MCP binary via native-build" as a **project**, not a lane. The
remaining work is breadth (14 kinds, 75 sites, 3-4 genuine projects) plus at
least two entirely unmeasured phases behind it. Clearing one more gap would not
change that conclusion, which is why this assessment exists instead of another
fix.

If a local MCP server is wanted sooner, the interpreted lane is worth pricing
separately: the pure-Simple compiler runs the MCP source today under the seed,
and none of the 75 diagnostics above apply to it. That was not evaluated here.

## NOT verified

- Whether any of the 14 kinds share a root cause. `undefined variable`'s 7 names
  and `new`'s 8 sites are the likeliest to collapse; neither was traced.
- Nothing beyond the MIR phase, at all.
- The interpreted-lane alternative in the recommendation is a suggestion, not a
  measurement.
