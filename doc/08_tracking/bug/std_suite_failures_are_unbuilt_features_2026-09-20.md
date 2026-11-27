# Triage: the 9 `test/01_unit/std` failures are unimplemented features, plus one real concurrency defect

- **id:** std_suite_failures_are_unbuilt_features_2026-09-20
- **status:** OPEN — triaged, not fixed; one item is a genuine defect worth owning
- **severity:** P3 for the suite as a whole (it reads as 9 regressions and is mostly not), P2 for the threading item
- **found:** 2026-09-20, running `test/01_unit/std` — a surface that had never been run in this session's sweep

## Result

```
test/01_unit/std   944 specs, 935 passed, 9 failed, 0 terminated
```

The cleanest surface measured in the whole sweep. All 9 failures are **identical
on the pre-deployment binary**, so none is a regression from this session's five
landed fixes.

## Why this needs saying: none of the 9 carries an in-development tag

Checked individually — no `@tag:in-development`, no `# @pending`, no `# @skip`
on any of them. So to anyone reading the suite output they look like nine
regressions. Seven of them are not defects at all; they are specs for
**functionality that was never built**.

| failure | error | nature |
|---|---|---|
| `perf_optimization_spec` ×4 | `type mismatch: cannot convert enum to int` | **real defect** (see below) |
| `spipe_before_all_after_all_spec`, `spipe_alias_before_after_all_export_spec` | ``semantic: function `before_all` not found`` | test-framework feature not implemented |
| `mock_simple_spec`, `mock_phase6_spec` | ``semantic: variable `Mock` not found`` | mock framework not implemented |
| `mock_phase5_spec` | ``✗ chains when with returns -- expected 0 > 0`` | mock framework |
| `parser/treesitter_node_spec` | `Module "std.parser" does not export 'treesitter_node'` | module does not exist anywhere under `src/lib` |
| `feature_validation/codegen_spec` | ``✗ proves each arm reached the engine it names`` | codegen feature probe |
| `no_paren_test` | `no parseable pass/fail summary in test output; refusing synthetic pass` | runner correctly refuses to invent a verdict |

`treesitter_node` was checked directly: no file, no symbol, nothing under
`src/lib` defines it. `before_all`/`after_all` and `Mock` are the same shape —
the spec describes an API the tree does not provide.

**These are dev work in substance even though untagged.** Implementing
`before_all`/`after_all`, a Mock framework and treesitter node support is three
feature projects, not three bug fixes. The actionable item here is arguably to
*tag* them, so the suite stops reporting unbuilt features as failures — but
that is a call for whoever owns those roadmaps, not a unilateral edit.

## The one real defect

`test/01_unit/std/perf_optimization_spec.spl` — 47 of 51 pass; the 4 failures
are all **threading/channel**:

```
✗ runs 5 threads with accumulation
✗ thread produces main consumes
✗ spawns 50 explicit-argument threads
✗ sends and receives 100 messages
```

all with `semantic: type mismatch: cannot convert enum to int`. Neither `enum`
nor `int` appears in the spec's own 569 lines, so the mismatch arises inside the
concurrency layer the spec calls, not in the spec.

Not pursued further here, and the reason is worth stating rather than implying:
it is in an area this session never touched, an isolation probe did not
reproduce it cleanly on the first attempt, and an open-ended concurrency
investigation is a different piece of work from a test-triage pass. It is
recorded so it is not lost, with the exact four example names and the error, so
whoever owns threads can start from a known repro rather than from scratch.

## Related

- `doctest_surfaces_registered_but_not_executed_2026-09-19` — same theme from the
  same sweep: a surface that looks maintained and is not.


---

## Lane disposition 2026-11-13 (p3-misc-b)

triaged in-file: unimplemented features plus one genuine concurrency defect owned elsewhere.
## Addendum 2026-11-13 — lane lp5 (worktree lp5-wt): re-run at tip

`test/01_unit/std/perf_optimization_spec.spl` now runs 54 examples (was 51): 51 pass,
3 fail. The 4 threading failures recorded 2026-09-20 have drifted with the tree; the
current 3 are "reports done immediately for PureStd" (asserts `is_done()` immediately
after `spawn_thread` — the spec's own sibling example documents that as a race:
"Spawn runs on a real OS thread, so is_done() right after spawn is a race"),
"spawn_isolated2 works in native mode" and "spawns 50 two-arg threads" (both need the
native concurrent backend under the seed interpreter). These are
concurrency-runtime/compiler-behavior dependent (the record's own classification: P2,
owned by the threads lane), not assertion drift this lane can safely edit — changing the
race-asserting example would un-pin a real behavior. The 7 unimplemented-feature rows
(mock/before_all/treesitter/codegen) stand as recorded (feature projects, tagging is a
roadmap-owner call).
