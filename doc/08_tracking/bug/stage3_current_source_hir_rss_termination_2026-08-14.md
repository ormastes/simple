# Current-source Stage 3 terminates after unbounded HIR build RSS growth

- Status: OPEN
- Date: 2026-08-14
- Severity: P0 bootstrap blocker
- Owner: pure-Simple compiler/bootstrap memory lifecycle

## Reproduction

A single-writer, cache-preserving pure-Simple Stage-3 build used the
provenance-retained Stage-2 parent with LLVM, one worker, `dynload`, the
core-C-bootstrap runtime, and `SIMPLE_NO_STUB_FALLBACK=1`. After the HIR
contract model fix removed the prior Phase-3 unresolved-name diagnostic, two
retries were externally terminated and produced no candidate. Cycle 2's log
does not retain its exit or RSS; cycle 3 retains the signal/time/RSS below but
not a reliable outer-wrapper exit status.

The final bounded cycle retained `/usr/bin/time -v` evidence in
`build/native_probe/stage3-fresh/build-cycle3.log`:

```text
Command terminated by signal 15
Elapsed (wall clock) time: 12:51.93
Maximum resident set size (kbytes): 24839624
```

The compiler emitted no error after its initial three source diagnostics, and
the cache contained no completed object. This report does not infer that the
kernel OOM killer sent the signal; the authoritative facts are the measured RSS,
signal 15, absent candidate, and absent compiler diagnostic.

This is a current-source recurrence of the symptom family tracked in
`stage3_frontend_hir_unbounded_memory_growth_2026-08-10.md` (large HIR-phase
RSS followed by external termination). It does not yet prove the same retained
owner or termination mechanism, so that older report remains the investigation
authority and this record binds the Restart-12 reproduction/evidence.

## Exact and adjacent acceptance

1. Profile the current pure-Simple parse/HIR closure and identify the retained
   owner responsible for the growth; do not delete the shared cache or switch
   to the Rust seed.
2. Add an exact full-entry-closure memory regression plus an adjacent bounded
   multi-module build proving that transient module state is reclaimed without
   losing cross-module metadata.
3. Re-run one canonical Stage-3 transaction. It must finish within the selected
   bootstrap RSS budget, emit a provenance-bound candidate, pass sanity, and
   compile/run the hello plus module-qualified field-layout regression.

Three build/fix cycles were consumed in this session. Resume in a fresh scoped
session; do not repeat the unchanged command here.

## Retained-evidence audit (2026-08-14)

The retained cycle does **not** identify an allocation or retention owner.  It
proves only the command high-water mark and external termination.  In
particular:

- `build-cycle3.log` contains no `BOOTSTRAP-PHASE` records because
  `SIMPLE_COMPILER_PHASE_PROFILE=1` and its durable sink were not enabled;
- the hard-coded `bootstrap-error-count` probe names only source indexes 0--2,
  then becomes silent, so the two later `hir-field-type` lines cannot bind the
  high-water mark to a source path or source index;
- `actual=2589120870` on `CompiledUnit.entry_point` and `BackendError.span` is
  the stable Optional-kind discriminant already documented by
  `stage3_selfhost_nonterminating_reexport_chase_2026-08-06.md`; it is not an
  allocation counter or evidence of corrupt type storage; and
- the August 10 process-chain incident cannot explain away this measurement:
  GNU `time -v` reports the timed command/descendant high-water mark, but the
  retained run has no contemporaneous process-tree or heap-counter series with
  which to distinguish runtime-value heap, raw allocations, or another child.

Therefore no pure-Simple memory fix is evidence-backed yet.  Changing an HIR
accumulator or inserting an AST reset from this log alone would violate the
first-root rule and repeat hypotheses already refuted by the August 10 bounded
sweeps.

## Next fresh-session instrumentation (one build, no blind retry)

The next permitted canonical transaction must capture all of the following in
the **same** run before any source fix is selected:

1. Set `SIMPLE_COMPILER_PHASE_PROFILE=1` and
   `SIMPLE_COMPILER_PHASE_PROFILE_FILE=<retained-path>` so every existing
   `phase3:hir:file:start/done` marker is durable across SIGTERM.
2. Do not rely on the current `log_mem_snapshot` stderr line: native-build
   worker stderr is dropped by the capture/relay path, so SIGTERM can erase the
   decisive counters.  First add a dedicated
   `SIMPLE_MEM_SNAPSHOT_FILE=<retained-path>` sink (or reuse another facility
   only after proving equivalent guarantees) with this contract:
   - resolve and validate the parent and target without following symlinks;
     reject a symlink in any writable path component and reject a non-regular
     existing target;
   - create with exclusive/no-follow semantics, retain one writer-owned file
     descriptor, append complete newline-terminated records, and flush each
     record before returning to compiler work;
   - never truncate or replace an existing receipt, and fail closed before the
     measured build if safe append-only publication cannot be established;
   - record schema/version, compiler PID, monotonic time, phase, source index,
     the source path recorded by the driver, `rt_heap_live_bytes`,
     `rt_heap_peak_bytes`, process RSS/HWM, and the scalar cardinalities named
     in item 4.  Label that path canonical only if the sink separately resolves
     it and verifies the resolved identity against the opened source; and
   - close with a terminal record on normal completion.  A missing terminal is
     valid interrupted evidence only when every preceding flushed record
     remains parseable and sequence-contiguous.

   With that durable sink active, place gated snapshots at HIR file start,
   post-lowering, post-diagnostics, and post-store.  Add deliberate-red tests
   for symlink parent/target, pre-existing target, partial record, sequence gap,
   and killed-writer retention before accepting its measurements.  The heap
   counters then distinguish retained runtime-value heap from untracked/raw
   RSS without depending on stderr delivery.
3. Sample the compiler PID and its descendants from `/proc` at ten-second
   intervals, retaining `VmRSS`, `VmHWM`, `RssAnon`, `RssFile`, PID, PPID, and
   argv.  These samples establish process-tree hygiene and coarse RSS shape;
   they are not authoritative for per-source attribution.  The flushed
   per-boundary sink records from item 2 are authoritative at HIR boundaries.
   Fail the evidence run if an unrelated `simple replay` chain or an unexpected
   build child appears.
4. At each HIR boundary record scalar cardinalities only: retained module
   count, validation key/value counts, shared trait count, and the outer lengths
   of `_bootstrap_hir_module_names`, `_bootstrap_hir_module_symbols`,
   `_bootstrap_hir_module_functions`, `_bootstrap_hir_module_constants`,
   `_bootstrap_hir_module_enums`, `_bootstrap_hir_module_structs`, and
   `_bootstrap_hir_module_classes`.  Do not stringify or copy HIR aggregates
   for diagnostics.
5. No numeric per-module limit is selected by current requirements or retained
   evidence.  Attribute the first boundary with a monotonic positive jump in
   RSS or `rt_heap_live_bytes` that is not reclaimed at the next completed
   module boundary, then confirm the same owner/phase shape in the exact
   reproducer before calling it retention.  If growth is reclaimed or moves to
   a different owner, the run has not identified the root.  Only after that
   confirmation add the adjacent multi-module retention regression and
   implement the narrow owner-side fix.

This instrumentation makes one fresh build discriminating: a rising
`heap_live_bytes` selects the runtime-value allocation/retention domain for
investigation, not an owner or leak until reproducer confirmation; flat heap counters with
rising `RssAnon` select raw/native allocation; a new descendant selects process
fan-out; and a bounded per-module sawtooth refutes unbounded retention.
