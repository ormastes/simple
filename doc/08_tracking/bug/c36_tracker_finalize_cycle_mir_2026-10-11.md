# C36 tracker finalization and cycle MIR failures

Tracking: https://github.com/ormastes/simple/issues/2998 (label `bug`).
Status: source repair; native manual replay and regression execution pending.

## Actual producer evidence

Source `f25bf97f47c021359e5321e1c8ae0b584d1cce4f`, producer C36
`5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`, entry `src/compiler/40.mono/monomorphize/tracker.spl` passed HIR
for its 11-module closure, then failed MIR before object emission. Exit 1,
71.998 seconds, zero actual tests. Retained evidence:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36/mono-tracker/{result.json,build.log,launch.json}`.
The SCV was `45ba6fe061e122c2d1e9ddda80a53f2e3034ad6067a9e49beabdfc5121eec090`.

## Source/API defects

`InstantiationTracker` exposes free new/finalize functions, but finalize called
undeclared flush_pending_deps/analyze_cycles methods. `NoteSdnMetadata` has no
clone method. The original port's Rust finalize consumes self: flush only
pending dependencies whose source is tracked, then analyze cycles, then return
owned metadata. The Simple implementation now explicitly snapshots the metadata
and performs those operations on the returned snapshot. It does not mutate the
caller's retained tracker or silently share mutable rows/arrays. Existing rows,
errors/warnings and optional build settings are retained; array containers,
record rows and nested build arrays are reconstructed. Snapshotting does not
republish specialization facts through add_instantiation/add_possible.

The cycle detector also used nonexistent CircularWarning.warning_code;
the real field is severity and the original implementation supplies `warning`.

## Narrow source workaround

Text clone calls operated only on immutable text, not on graph or metadata
collections. The immutable view contract is documented at
`src/lib/nogc_async_mut_noalloc/string/mod.spl:4` and the canonical text design
`doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md`.
Retaining those text values preserves their value semantics; mutable metadata
still uses explicit snapshots. No unsafe string buffers are exposed here.

C36 loses `[text]` provenance after `if val neighbors = graph.get(key)`:
for-in sees MIR I64 at cycle_detector lines154/350/412. Workaround #2998 uses
contains_key followed by a typed bracket read. Missing keys still skip traversal;
an empty present adjacency remains an empty traversal. It does not widen loop
admission or alter graph search/order/classification algorithms. The underlying
optional dictionary collection provenance defect remains open.

## Verification

`test/fixtures/compiler/tracker_finalize_snapshot/main.spl` asserts pending
eligibility, hard/soft diagnostics, DAG/topological/prospective-cycle behavior,
missing adjacency, repeat finalization, and row/nested-array isolation.
Runtime assertions are authored and unexecuted. Existing
`test/01_unit/compiler/mono/cycle_detector_soft_edge_index_spec.spl` remains
applicable. Source files in this repair match frozen C36 before these edits.
No frozen tree was edited; no compiler build or native command was run here.
Independent source review and coordinated actual manual replay are required.
