# Current-source Stage 3 terminates after unbounded HIR build RSS growth

- Status: OPEN
- Date: 2026-08-14
- Severity: P0 bootstrap blocker
- Owner: `/root/memory_sink_impl` — pure-Simple compiler/bootstrap memory lifecycle

## 2026-08-14 owner fix (pending one future canonical build)

Static localization found a retained aggregate boundary after the earlier
scalar surface-index repair: the non-streaming Stage3 HIR loop constructed a
fresh `HirLowering` for every source and passed the complete frozen
`ModuleSurfacesByName` into every constructor. In the no-GC Stage3 process,
that made the closure-sized registry a per-module retained value. The shared
owner now constructs one explicitly typed lowerer before the loop and calls
its existing `begin_module` reset for each source. That reset preserves the
single frozen surface registry, accumulated traits, and stable diagnostic
owners while replacing transient module state.

Focused contracts are
`test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl` and
the existing behavioral `hir_lowering_begin_module_spec.spl`. This source fix
does not close the bug: the required next evidence is one cache-preserving
canonical Stage3 transaction under the selected RSS budget, followed by
candidate provenance and sanity. No full bootstrap was run in this repair
lane.

Cycle-2 review found that outer reuse alone was incomplete because
`begin_module` still called `hirlowering_new()` and copied the retained surface,
trait, configuration, and re-export aggregates through locals on every source.
The reset now operates entirely in place: `SymbolTable.reset_module` clears and
reuses its root owner; module-local diagnostics, imports, implementation maps,
materialization maps, local type maps, glob memo, and re-export visit workspaces
are cleared; scalar state is reset directly. The frozen surface registry,
accumulated traits, inference configuration, and re-export root cache are left
untouched. The driver also no longer copies the accumulated trait dictionary
through a second local each iteration. Behavioral coverage now includes two
module transitions, transient-state sabotage/no-leak assertions, retained
surface/config checks, and a 64-reset heap-registry plateau oracle. The bug
remains OPEN pending executable evidence from a current full CLI and the single
future canonical Stage3 transaction.

Cycle-3 removed the same constructor/trait-copy pattern from the source-less
compatibility loop and replaced the reset's extracted `Scope` value with a
persistent root-symbol dictionary owner. Nested field/type maps are cleared at
their outer owner and repopulated in the two-module sabotage test, exercising
logical COW detachment without copying them through reset locals. No truthful
byte proof was retained in that cycle: `rt_heap_registry_count` measures
registry slots, not allocated bytes, so that earlier proxy oracle was removed.
Allocation/RSS boundedness therefore remained explicitly UNPROVEN pending a
real byte-counter lifecycle oracle or the future profiled Stage3 transaction;
the static contract proved only that neither HIR loop nor `begin_module`
reconstructs a lowerer or copies retained surface/trait owners.

Cycle-4 review rejected a proposed synthetic populate/reset plateau oracle.
The Rust hosted `rt_heap_live_bytes` counter measures registered runtime-value
header/inline bytes and `rt_heap_aux_live_bytes` measures collection backing
buffers, but both are process-global. The core-C compatibility provider with
the same first name reports only opt-in/manual SPL memtrack entries and does
not cover `runtime_native.c` RuntimeValue allocations. Reads around an SSpec scenario cannot attribute changes to
one `HirLowering`, exclude runner/matcher allocation, cover uninstrumented raw
allocations, or establish the production `lower_module` lifecycle. Exact
equality would therefore be a fragile diagnostic checkpoint, not an owner
proof. The oracle and its proof claim were removed rather than weakening the
P0 gate. An acceptable focused proof still requires either an attributable
HirLowering arena/generation owner covering nested backing/raw allocations and
real `lower_module`, or an isolated native lifecycle probe using the exact
Stage3 runtime. Neither exists in this lane, so memory boundedness and RSS
termination remain **EVIDENCE FAIL**.

A no-stub, one-worker Cranelift mini-build of
`module_surface_physical_alias_native_probe.spl` was attempted with the retained
Stage2 and an isolated `build/mini_cache_stage3_hir_owner` cache. It stopped
during discovery on the current frontend's newer `convert_nodes.spl` grammar
(`626:43`, newline where that older compiler expected an expression), before
the changed HIR owner was compiled. The retained diagnostic is
`build/mini_builds/stage3-hir-owner/build.log`; it is neither a failed owner
test nor acceptance evidence. The bootstrap-only Stage2 also has no `test`
command, so focused SSpec execution awaits the future full CLI.

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

## Restart-12 actor/process continuation evidence

A typed-receipt full-bootstrap transaction produced and sanity-admitted a
current-source pure-Simple Stage 2 (SHA-256
`4c2d7d7328372175260d75ffd1ee2e475d9848a1d534c73ace7a9ef1eee0b68e`).
Its Stage-3 child advanced to parse file 200/617, then grew monotonically from
2,713,164 KiB through 29,019,120 KiB RSS and was externally terminated with
status 143. The compiler emitted no diagnostic and produced no candidate.
The durable series is retained at
`build/bootstrap-restart12-current/bootstrap-retry-progress.log`.

This confirms the P0 remains reproducible with a current admitted Stage-2
authority. It does not identify the retained allocation owner, so the next
cycle must consume the existing durable instrumentation and root-cause the
growth; an unchanged rebuild is prohibited.

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
   counters distinguish retained runtime-value heap from untracked/raw RSS only
   when the selected provider is proven to cover RuntimeValue allocation and
   registry lifecycle. The current core-C provider does not.
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
   evidence. Attribute the first boundary with a monotonic positive jump in
   RSS; use `rt_heap_live_bytes` only with a provider whose RuntimeValue
   coverage is proven and whose value is not reclaimed at the next completed
   module boundary, then confirm the same owner/phase shape in the exact
   reproducer before calling it retention.  If growth is reclaimed or moves to
   a different owner, the run has not identified the root.  Only after that
   confirmation add the adjacent multi-module retention regression and
   implement the narrow owner-side fix.

This instrumentation makes one fresh build partially discriminating. On the
Rust hosted provider a rising `heap_live_bytes` selects the runtime-value
allocation/retention domain for investigation, not an owner or leak until
reproducer confirmation. On current core-C it is only an opt-in/manual SPL
memtrack total and cannot select or exclude that domain. Rising `RssAnon`
remains coarse raw/native evidence; a new descendant selects process
fan-out; and a bounded per-module sawtooth refutes unbounded retention.

## Durable snapshot implementation (2026-08-14)

The fresh-run prerequisite is implemented, but this lane did not start the
canonical Stage-3 transaction. `compiler.driver.driver_mem_snapshot` is the
single environment/config and descriptor owner. Runtime-owned bounded-stack
formatting receives scalar fields, avoiding a Simple no-GC text-allocation
slope. Runtime/core-C and hosted-interpreter owners descriptor-walk parents
with `openat(O_DIRECTORY|O_NOFOLLOW)`, create the leaf with
`O_EXCL|O_NOFOLLOW|O_APPEND`, retain one descriptor, and flush each record.

Snapshots cover file start, post-lowering, post-diagnostics, and post-store.
Retained-module and shared-trait counts are owner-maintained scalars; the probe
does not materialize `Dict.keys()`. The Stage-3 resume wrapper now transcribes
and forwards fresh retained phase-profile and memory-snapshot paths.

The focused core-C contract covers complete/interrupted writers, existing and
symlink targets/parents, token encoding, sequence continuity, and deliberate-red
partial/gap fixtures. It passed with C and shell syntax checks. Rust compiler
checking reached unrelated pre-existing missing
`simple_runtime::rt_provider_query_v1_call` symbols and emitted no snapshot-file
diagnostic. The three-cycle cap is exhausted; next is higher-capability source
review and then the single instrumented Stage-3 transaction.

## Rejected process-sampler design and required redesign (2026-08-14)

A proposed wrapper-owned Python sampler/analyzer was rejected after final
review and removed before any Stage-3 run. Python is not an admitted dependency
for this bootstrap evidence path, and changing the established provenance-v3
manifest would invalidate existing consumers. The redesign must remain within
the current v3 compatibility contract, or introduce a separately versioned and
explicitly migrated evidence receipt without silently widening v3.

The next implementation must launch the measured compiler in an isolated
process group, retain stable identities for the root and every discovered
descendant, and terminate/reap the entire group on normal exit, interruption,
or sampler failure. It must bind the executable by an opened descriptor and
verified device/inode/hash so path replacement between validation and exec
cannot change the measured authority. Record parsing must reject duplicate or
unknown keys, non-canonical numeric forms, overflow, negative values where
forbidden, inconsistent root PID/start identity, PID reuse, missing root
samples, and multiple or invalid terminal records.

Memory boundaries, process samples, and phase-profile records need a shared
run identity plus comparable monotonic timestamps; line order or approximate
wall time is not sufficient correlation. Derived boundary/delta/summary files
must be produced from descriptor-bound inputs into absent descriptor-walked
targets, flushed, hashed, and atomically admitted as one bound set. A failure
must leave only explicitly interrupted raw evidence, never a partial derived
set that resembles a completed analysis. Add deliberate-red coverage for each
rule before authorizing the one fresh Stage-3 transaction.

## Rejected C sampler/analyzer cycle and next boundary (2026-08-14)

A subsequent non-Python C sampler/analyzer attempt was also rejected and fully
reverted after its third permitted fix cycle. Stage 3 did not start. The draft
had added a bounded run identity, explicit storage/time caps, strict `/proc`
field handling, descriptor-bound ELF execution, and a child-setup handshake,
but those improvements did not make its termination evidence safe.

The sampler could still publish a terminal record after a fixed kill window
with live survivors, could block indefinitely while reaping, signalled PIDs
without rechecking their recorded start identity, and could signal a reused
process group after its root was reaped. Its discovery logic also missed
subreaper-adopted and `setsid` descendants. The next implementation must use
identity-checked signalling and bounded reaping, discover adopted and detached
descendants, and prove zero survivors. Otherwise it must publish only an
interrupted/failure raw receipt and must never claim a completed tree exit.

The paired analyzer must freeze one compatible strict record contract before
implementation. It needs distinct sampler, analyzer, and measured-command
device/inode/SHA-256 identities; the same safe run ID with a 64-byte maximum;
exact open/sample/terminal variants including command identity; complete-only
terminal semantics; analyzer identity in its receipt; and exact phase,
source-path, and monotonic-time correlation. Missing raw terminals and
`sampler-stopped` are not complete analyses. The separate derived receipt must
remain `simple-stage3-memory-evidence-v1`; provenance v3 remains unchanged.

The session's three-cycle cap is exhausted. Do not make a fourth sampler or
analyzer attempt, and do not start Stage 3, in this session. Resume in a fresh
scoped lane from this jointly frozen producer/consumer and zero-survivor
boundary.

## Restart12 H0 dispatch reconciliation

This record is the current TODO666 authority. M0 remains actionable, but its
incompatible full-bootstrap wiring draft, subsequent C sampler/analyzer, and
latest supervisor redo were rejected and reverted at their bounded three-cycle
boundaries.
Existing resume-only durable phase/memory sinks remain. Safe phase
O_EXCL/no-follow publication, canonical full-bootstrap sink wiring, the
zero-survivor process-tree RSS/signal contract under the inherited outer PGID,
and compatible provenance
remain unimplemented. After acceptance, a fresh session builds a
current-HEAD Stage 2 in a unique output and runs exactly one instrumented Stage
3, retaining phase, memory, process-tree, RSS, source/runtime/tool provenance,
manifests, logs, and hashes. Historical `e383...` predates the complete
`d99deb3` snapshot runtime provider. Its 41,394 MiB interrupted high-water mark
does not establish the completion RAM requirement or select Phase 2 parsing
versus Phase 3 HIR as owner. No fourth run is permitted in this session.

## Restart12 supervisor redo terminal review

A later three-cycle supervisor-only redo did not start Stage 3. It repaired the
earlier shell/Perl facade error, descriptor-walked exclusive receipt creation,
durable record writes, explicit x86_64-Linux gating, inherited outer-PGID
recording, identity-checked TERM/KILL, bounded configuration, and several
adversarial cases. Independent final review still rejected activation: any
post-fork handshake or evidence failure could exit without cleaning the child;
the deadline path could publish `survivors > 0` and abandon those processes;
and a complete sampling batch could exceed the advertised caps. The draft and
its focused test were reverted after the third cycle. TODO666 therefore retains
total cleanup from fork through exit, hard caps, zero-survivor termination,
strict analyzer/correlation, safe phase publication, full/resume wiring parity,
provenance migration, and the missing adversarial tests. This is a source/evidence
implementation blocker, not authorization for another Stage-3 run here.

## Restart12 phase/analyzer redo terminal review

Two further disjoint three-cycle drafts were rejected and reverted without a
Stage3 run. The phase publisher converged on descriptor-owned records, a shared
absolute `CLOCK_MONOTONIC` millisecond epoch, exact memory/phase timestamps,
explicit identities, terminal closure, and legacy-mode isolation. Final review
found that bootstrap-main's projected core-C capsule did not retain the three
new runtime providers, so the Simple driver could carry unresolved externs. The
strict analyzer converged on the actual memory/phase schemas, identity and clock
correlation, zero-survivor terminals, bounded records, descriptor-walked inputs,
and atomic no-replace publication. Final review found that a successful final
hard link followed by temp-unlink or directory-fsync failure could leave a
completed-looking receipt even though the analyzer returned failure. Both
drafts and their tests were reverted. TODO666 retains the exact capsule and
post-link rollback owners; no partial admission claim was made.

---

## RE-VERIFICATION 2026-08-17 (c_splmisc lane) — SOURCE FIX CONFIRMED PRESENT; VERIFICATION STILL GATED

Classified by CONTENT, not by SHA.

The doc's claim that "the owner fix landed source-side" is **confirmed** in
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`. The two allocation
behaviours that drove the unbounded HIR-build RSS growth are now explicitly
hoisted out of the per-module loop, each with a comment naming the intent:

- `:357` — "Allocate the diagnostics array before the long HIR loop and reuse
  its ..." (per-module diagnostics array no longer reallocated per source)
- `:466` — "This loop-owned lowerer is the trait registry owner. Do not copy"
  (single lowerer owns the shared trait registry across every module, rather
  than one lowerer per module)

Also present and consistent with the doc: the durable phase/memory diagnostic
sinks, gated behind `bootstrap_diag` (`:536`, `:604`, `:667`
`[bootstrap-error-count] ... point=post-lowering|post-diagnostics|post-store`),
plus the poisoned-module reporting at `:628-637`.

**COULD NOT PROVE — and this is the honest state of the row.** The doc's own
remediation requires a *cache-preserving canonical Stage 3 transaction*, i.e. a
full Stage 2 + Stage 3 bootstrap cycle. A user bootstrap was LIVE during this
session and is the stated top priority, so `build/bootstrap/**` was off-limits;
no bootstrap was started, resumed, or otherwise touched. Nothing here measures
RSS.

**Methodological warning for whoever resumes this, because this row is uniquely
exposed to it.** The bug's own signature is *status 143*. On this host (load
80-130, ~90 concurrent `simple` processes) a healthy run is routinely SIGTERMed
by a watchdog and ALSO exits 143 with no `Results:` line — indistinguishable by
exit code alone. Worse, a `kill_simple_monitor.shs` misconfiguration was live
until 06:35 today with `MIN_AGE_SECS=60`, below a normal spec's ~115s runtime.
**Do not accept 143 as a reproduction of this bug without an RSS trace.** The
distinguishing evidence is monotonic RSS growth across the HIR loop, not the
exit status. Any 143 observation on this row recorded before 06:35 today should
be re-run.

---

## 2026-08-17 (W2 driver lane) — FAMILY COLLAPSED; ROOT IS NOT IN 80.driver

These three rows were re-examined together as instructed, on the hypothesis that
one cause spans them (AST and HIR arenas live simultaneously):

- `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20`
- `stage3_current_source_hir_rss_termination_2026-08-14`
- `bootstrap_stage4_ast_hir_overlap_memory_2026-07-27`

**The hypothesis is right, and the root cause is already written down in source,
with probe numbers — in `src/compiler/80.driver/driver_types.spl:1080-1100`:**

> The three evictions below drop references only. With no GC and no refcounting
> that reclaims NOTHING -- measured at 0 of 2001 allocations by
> `src/runtime/test/rt_driver_eviction_reclaim_selfcheck.c` (probe P0).
> ... Unblocking this needs class instances to be identifiable at runtime, a
> codegen/representation change, **NOT a driver change**.

So `evict_sources()` / `evict_ast()` / `evict_hir()` / `evict_mir()` are all
no-ops on the bootstrap lane, which is exactly why "clears the AST dictionary
after HIR" never reduced the peak, and why moving the eviction earlier in the
loop cannot help either. The overlap described in the 07-27 row is not a
sequencing defect in the driver; it is that nothing the driver can call frees
anything. The two obvious driver-level "fixes" were both already tried and both
measured HARMFUL: `rt_dict_free_deep` frees key strings aliased from outside the
dict by HIR/AST/SymbolTable (use-after-free, probes P2/P3), and per-module
lowerer reconstruction is the retained-aggregate boundary the 08-14 row fixed.

### Verdict per row
- **08-14** — source fix CONFIRMED PRESENT and now guarded by a spec (single
  lowerer hoisted out of the loop, one reused diagnostics buffer, no
  surface/trait copies through per-iteration locals). Executable RSS evidence
  still requires one canonical Stage-3 transaction; not run (a user bootstrap
  was live and `build/bootstrap/**` was off-limits).
- **07-20 / 07-27** — **BLOCKED-CROSS-OWNER.** The remaining fix is a runtime
  representation change so that a class instance carries a tag/header the heap
  registry can identify, in `src/runtime/runtime_native.c` (heap registry /
  `rt_alloc` class-instance representation) plus the native class-layout emitter.
  Those files are outside the 80.driver ownership boundary, so nothing was
  edited there. No driver-side change can close these two rows.

### What was NOT measured, stated plainly
No RSS number was produced for the pure-Simple lane in this session. The only
figure obtained was **3,050,124 KiB peak RSS** (`/usr/bin/time -v`) for the
**Rust seed** `bin/release/x86_64-unknown-linux-gnu/simple` interpreting
`src/compiler/80.driver/main.spl --check <one tiny file>` — a different memory
model entirely, and therefore evidence for nothing on these rows. It is recorded
only so it is not mistaken later for a lane measurement. Per the 08-14 row's own
warning: on this host a status-143 exit is indistinguishable from an earlyoom or
watchdog kill, so **143 without a monotonic RSS trace is not a reproduction.**

### Family guard
`test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl` —
`Results: 5 total, 5 passed, 0 failed`. It fails if a deep-free call is
reintroduced into the driver context, if the measured hazard rationale is
deleted, or if the HIR loop goes back to constructing a lowerer per source.

---

## 2026-08-17 (P0 scoped lane) — GROWTH IS LINEAR-UNRECLAIMED, NOT AN ALGORITHMIC BLOWUP; STILL BLOCKED-CROSS-OWNER

Method: static source tracing plus arithmetic on the already-retained
Restart-12 series. **No new Stage-3 run was performed** and no new RSS number
was produced (see "What was not measured" below). Host load average at session
start 35.85, at 12:25 44.18 — any timing here is contended by construction.

### 1. The retained series is a LINEAR slope, which changes the diagnosis

From the Restart-12 numbers already in this record: RSS went 2,713,164 KiB at
parse file 200/617 through 29,019,120 KiB at external termination. That is
**25.1 GiB consumed across at most 417 further modules = >=63 MiB per module**,
against a measured **7,288 B mean `.spl` source size** (`find src/compiler
src/lib src/app -name '*.spl'`: 12,114 files, 88,284,967 B total). So each
module retains **>=8,600x its own source text**, and the series is *monotonic
and near-constant-slope*, not accelerating.

This is the discriminating observation the earlier cycles never made: a
quadratic/superlinear owner (retained aggregate copied per module, a growing
registry re-walked per module) would show a *rising* slope. A constant slope of
~63 MiB/module is the signature of **linear accumulation with zero
reclamation** — i.e. every module's AST+HIR simply stays live to the end of the
phase. That is consistent with, and independently corroborates, the
`driver_types.spl:1080-1100` probe-P0 finding that eviction reclaims 0 of 2001
allocations. It also *retires* the "retained aggregate boundary" hypothesis as
the dominant term: the 08-14 lowerer-hoist fix was correct and is still the
right shape, but it cannot have been worth 25 GiB.

### 2. Stage 3 runs with `low_memory == false` — every gated eviction is OFF

Traced in source, no run required:

- `src/compiler/80.driver/bootstrap_api_low_memory.spl:4-9` requires all three
  of `SIMPLE_BOOTSTRAP`, `SIMPLE_BOOTSTRAP_STAGE4`, `SIMPLE_BOOTSTRAP_LOW_MEMORY`
  to be `"1"` (predicate `bootstrap_low_memory_opt_ins_requested`,
  `src/compiler/00.common/bootstrap_low_memory_config.spl:6-11`).
- The **only** producer of those two latter variables, and of the `--low-memory`
  flag, is `bootstrap_native_build_main()` —
  `scripts/bootstrap/bootstrap-from-scratch.sh:1062-1095` — which is the
  **Stage 4** builder (`--entry src/app/cli/main.spl`).
- The **Stage 3** invocation (`scripts/bootstrap/bootstrap-from-scratch.sh:2068-2102`)
  passes neither the flag nor those variables. Therefore
  `ctx.options.low_memory == false` for the whole Stage-3 transaction.

Consequently these are all inert on Stage 3:
`driver_orchestration.spl:137` (source reclaim), `:175` and `:240`
(`evict_ast`), `driver_aot_pipeline.spl:88` and
`driver_pipeline_execution.spl:19` (`evict_hir`),
`driver_aot_native_output.spl:550` (MIR eviction), and the
`not ctx.options.low_memory` content-retention branch at
`driver_hir_pipeline_lowering.spl:513`.

### 3. …but enabling it would not fix this, and the number says so

The streaming-surface HIR path *is* live on Stage 3, contrary to what the
`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0` comment at
`bootstrap-from-scratch.sh:2061` suggests on a first read:
`driver_streaming_surface_enabled` (`driver_orchestration.spl:28-36`) requires
`ENTRY_CLOSURE == "1"`, and the driver's own closure walk sets exactly that at
`driver_source_pipeline_loading.spl:262` before HIR runs. So
`driver_hir_pipeline_lowering.spl:334-341` already executes `ast_reset()`,
`phase_ctx.modules = {}`, `lexer_release_parse_source_globals()` and an
**unconditional** `reclaim_source_contents()` on Stage 3.

`reclaim_source_contents` (`driver_types.spl:1057-1063`) is the one path that
genuinely frees, because `rt_string_free` is registry-checked and source text
is a registered RuntimeValue. Its entire ceiling is the Stage-3 closure's
source text: 617 modules x 7,288 B ~= **4.4 MiB, i.e. 0.018% of the 25.1 GiB
growth.** Turning on `--low-memory` for Stage 3 would therefore be a defensible
tidy-up but is **not** a fix for this P0, and must not be presented as one.
No such change was made in this lane.

### 4. Confirmed: the remaining owner is a runtime representation change

Re-derived independently this session with fresh citations, agreeing with the
W2 verdict:

- Class/struct instances are allocated as bare `rt_alloc` blocks with no header
  and no registration: LLVM lane
  `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl:105-135`;
  Cranelift lane `backend/cranelift_codegen_adapter.spl:623-633`.
- `rt_alloc` (`src/runtime/runtime_native.c:5506-5530`) is `malloc` +
  `rt_core_transient_raw_register`, which is a **no-op unless a transient array
  scope is active** (`:1331-1345`) — so there is no permanent registration and
  no kind byte.
- The runtime states the blocker itself at `runtime_native.c:6041-6058`
  ("SECOND LIMIT"): an instance "carries NO kind header, is NOT heap-tagged, and
  is NOT in any registry", so `rt_core_deep_free_classify` (`:6147`) must call
  it LEAF; fixable "only upstream, by giving `rt_alloc`'d aggregates a kind
  header or an unconditional registration."
- Nearest existing hook: the unused-from-Simple `rt_struct_alloc` /
  `rt_struct_alloc_register` / `rt_struct_alloc_lookup_size` ptr->size table
  (`:5344-5348`, `:5439`, `:5484`, `:5536`; declared `runtime.h:309-310`; no
  `.spl` emitter calls it).
- Scope of the real fix: both aggregate emitters (incl. their Tuple cases),
  a new registering `rt_object_new`, a new deep-free kind + child-word scan in
  `runtime_native.c`, `runtime.h`, and regenerated `runtime_symbol_entries.rs`.
  **The risky part is not the registry — it is that a header word shifts every
  struct field GEP in two backends, which must stay byte-identical with
  `translate_get_field`.** Hazard 4 (external key aliasing, probe P3) is *not*
  addressed by any of it.

**Backend asymmetry, not previously recorded here, and possibly a cheaper way
in.** The two lanes do *not* represent structs the same way. Cranelift ORs a
`heap_tag = 1` into the struct base pointer
(`cranelift_codegen_adapter.spl:631-633`), so a Cranelift struct pointer has low
bit 1 and does **not** satisfy the classifier's LEAF precondition ("`>= 4096`
with low bits `0b000`", `runtime_native.c:6147`). The LLVM lane yields the raw
`rt_alloc` pointer untagged (`aggregate_intrinsics.spl:127-135`) — and LLVM is
the bootstrap default backend, i.e. exactly the lane this P0 reproduces on.
Whoever picks this up should check whether the Cranelift tagging convention can
be adopted by the LLVM aggregate lowering, since a low-bit tag costs no header
word and therefore **does not shift any field GEP** — which is the expensive,
risky half of the change scoped above. This is an untested reading of the two
emitters, not a proposal that has been validated; the tag's interaction with
`translate_get_field` addressing and with every other consumer of a struct
pointer has not been checked.

That is outside `80.driver` ownership and cannot be validated without a full
bootstrap, so nothing was edited there. **Row stays OPEN / BLOCKED-CROSS-OWNER.**

### What was NOT measured, stated plainly

- No Stage-3 run. This worktree has **no `build/bootstrap/stage2` or `stage3`
  at all** (only `logs/`, two `rust-authority-*` dirs, `stage4-owner-20260815`),
  so acceptance item 3 would require a full multi-hour bootstrap from scratch on
  a box at load 35-44 with ~20 foreign `bin/simple` processes. Not attempted.
- **The durable evidence this record points at is GONE from this worktree:**
  `build/bootstrap-restart12-current/bootstrap-retry-progress.log` and
  `build/native_probe/stage3-fresh/build-cycle3.log` do not exist here. The
  Restart-12 figures above are therefore quoted from *this document*, not
  re-read from a retained artifact. Whoever resumes should not assume those
  logs are recoverable.
- `bin/simple` in this worktree is the **Rust seed** (it prints the seed
  banner), so it cannot produce pure-Simple-lane RSS evidence for this row.
- The 08-14 warning still stands: status 143 without a monotonic RSS trace is
  not a reproduction of this bug.

### Guard evidence executed today (both green, on the seed)

| spec | verdict | wall | peak RSS |
|---|---|---|---|
| `driver_memory_lifecycle_family_spec.spl` | `5 total, 5 passed, 0 failed` exit 0 | 13:46.53 | 3,347,772 KiB |
| `stage3_hir_lowerer_reuse_contract_spec.spl` | `4 total, 4 passed, 0 failed` exit 0 | 11:02.83 | 3,353,964 KiB |

Host load average 44.18 at launch, 28.07 at finish — contended, and both runs
were on the **Rust seed**, so the ~3.35 GiB figure is that interpreter's
per-spec baseline (cf. the W2 lane's 3,050,124 KiB for a one-file `--check`).
It is **not** a measurement of this bug's lane and must not be quoted as one.
Both specs are source-TEXT contracts; passing them fences the fix's shape and
proves nothing about RSS.

### 2026-08-22 driver promotion-attribution instrumentation

The streaming HIR driver now records two v1 memory-snapshot rows per source:
`hir-promotion` attributes the initial canonical HIR graph, while
`hir-promotion-total` records the transient scope's cumulative promoted nodes
and bytes after diagnostic, flat-HIR-row, and frontend-registry owners have
also promoted. Cache hits record zero for both rows because they open no
transient scope. The receipt field schema is unchanged: the existing
`retained_modules` and `validation_keys` columns continue to carry promoted
nodes and bytes for promotion phases. This is attribution instrumentation, not
a Stage-3 RSS fix or closure evidence; the bug remains open pending a canonical
instrumented Stage-3 transaction.

`stage3_hir_lowerer_reuse_contract_spec.spl` was found **RED on arrival** at
`4 total, 3 passed, 1 failed`: the example "validates compatibility spellings
through physical source identity" died with `semantic: variable source_idx not
found`. That was a defect in the SPEC, not the driver — the anchor literal
spelled the driver line out in full including `index={source_idx}`, and Simple
interpolates `{...}` in the spec's own string, so the example aborted while
building its anchor, before any comparison ran. The three examples that guard
this row's actual owner fix were passing throughout.

Fixed by truncating the `end` anchor to stop before the brace. Verified first
that this was not masking a second failure: the anchor text exists verbatim at
`driver_hir_pipeline_lowering.spl:731`, `var validation_surface_index: i64 = -1`
occurs exactly once (`:690`), and all six positive assertions plus the negative
one resolve inside the extracted 690..730 range (`:714`, `:718`, `:699`/`:719`,
`:691`, `:692`, `:701`/`:721`; `module_surface_index_for_source(` appears
nowhere in the file). No assertion was weakened or removed and the driver was
not touched.

### 2026-08-22 recovery snapshot ABI blocker

A fresh Stage 2 was admitted, but its first Stage 3 recovery stopped at HIR
entry with `SIMPLE_MEM_SNAPSHOT_FILE could not be established safely`.
`strace` showed no `openat` attempt. At a GDB breakpoint,
`rt_mem_snapshot_open` received a boxed Simple text value in `rdi` and zero in
`rsi`; the runtime provider requires `(byte_ptr, byte_len)`. The memory and
phase-profile owners now lower this raw SFFI boundary explicitly with
`rt_string_data` and `rt_string_len`. Another Stage 2 admission is required
before Stage 3 can be retried because the admitted compiler embeds the old
call site.

### 2026-08-22 rebuilt Stage 2 and first durable promotion evidence

The raw-boundary audit found a second instance of the same defect:
`rt_mem_snapshot_record` still passed three boxed Simple `text` values to a C
provider whose ABI is `(byte_ptr, byte_len)` for each value. The initial file
was therefore created successfully but remained zero bytes when its first
record was rejected. The driver now lowers `event`, `phase`, and `source_path`
explicitly through `rt_string_data` / `rt_string_len` in both snapshot owners.

A fresh four-job Stage 2 at `9c3cc6b4048` passed sanity and the struct receiver
proof and was admitted. The canonical Stage 3 recovery then showed one
intermittent SIGSEGV during streaming surfaces at sequence 62. A debugger run
with the identical admitted compiler, environment, one-thread mode, and cache
passed all 688 surfaces and entered HIR. Its durable first-module rows are:

| row | promoted nodes | promoted bytes | RSS | HWM |
|---|---:|---:|---:|---:|
| `hir-promotion` | 13,485 | 419,955 | 640,932 KiB | 688,312 KiB |
| `hir-promotion-total` | 38,060 | 1,218,945 | 640,932 KiB | 688,312 KiB |

The debugger transaction was externally terminated while module 1 was still
lowering. Its live backtrace was in `rt_transient_raw_insert` via `rt_alloc`,
under a repeating chain of `register_imported_symbol_inner`,
`materialize_imported_field_dependency_inner`, and
`register_imported_type_methods_inner`. This is measured evidence of recursive
import-materialization fan-out in the allocation hot path; it does not yet
prove whether the termination is caused by a cycle, repeated acyclic work, or
an ownership lifetime defect. The row remains OPEN pending a visited/in-flight
audit of those three functions and a canonical Stage 3 completion.

## 2026-09-06 (aarch64 measurement lane) — THE RUNTIME ALREADY RECLAIMS AGGREGATES; THE BINDING CONSTRAINT IS TRANSIENT-SCOPE COVERAGE, NOT A MISSING HEADER WORD

Host: aarch64 Linux, 20 cores, 121 GiB RAM, load average 12-45 during the runs
(contended by construction — treat wall times as an envelope, not a floor).
Binary identity recorded with every number below:

```
readlink -f bin/simple
  /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple
stat -c '%s %y'  ->  50093192  2026-09-06 09:59
bin/simple --version | tail -1  ->  Simple Language v1.0.0-rc.1
  (banner: "this Rust-built Simple binary is a bootstrap seed only")
```

### 0. Retained-evidence audit, repeated

`build/native_probe/stage3-fresh/build-cycle3.log` is **still gone**, and this
worktree has **no `build/bootstrap/stage2` or `stage3`** either (`ls -d
build/bootstrap/stage*` -> no such file). The Restart-12 figures remain quoted
from this document. No canonical Stage-3 transaction was run in this lane, and
acceptance item 3 is therefore still open.

### 1. Measured: an rt_alloc'd aggregate outside a transient scope is never freed, at 16 + 8*fields bytes each

Fixture (JIT-compiled by the seed — `bin/simple run` reports **no**
`[jit-fallback]`, so this is the native C runtime, not the Rust interpreter):

```simple
class Node:
    a: i64
    b: i64
    c: i64
    d: i64

fn main():
    var n: i64 = 0
    var sum: i64 = 0
    val limit: i64 = 1000000        # varied per row
    while n < limit:
        val node = Node(a: n, b: n + 1, c: n + 2, d: n + 3)
        sum = sum + node.a
        n = n + 1
    print "sum={sum}"
```

Command per row: `/usr/bin/time -v ./bin/simple run <fixture>.spl`, reading
`Maximum resident set size (kbytes)`.

| fixture | allocations | max RSS (KiB) | marginal B/alloc |
|---|---:|---:|---:|
| `Node` (4 x i64) | 100,000 | 40,332 | — |
| `Node` (4 x i64) | 1,000,000 | 84,780 | 50.6 |
| `Node` (4 x i64) | 4,000,000 | 225,484 | **48.03** |
| `Node` (4 x i64) | 8,000,000 | 412,848 | **47.97** |
| `Node8` (8 x i64) | 1,000,000 | 115,840 | — |
| `Node8` (8 x i64) | 4,000,000 | 350,172 | **79.99** |
| `[i64]` of len 4 | 1,000,000 | 124,320 | — |
| `[i64]` of len 4 | 4,000,000 | 402,852 | **95.07** |

The slope is constant to within 0.1% across an 80x input range, and 4 -> 8
fields moves it by exactly 32 B (8 B/field, 16 B fixed). That arithmetic
attributes the retained bytes to the **instance block itself**, not to the loop,
the JIT, or allocator fragmentation. Every instance the program drops stays
resident for the life of the process. Arrays leak on the same path, so this is
not specific to class/struct aggregates.

### 2. Measured: wrapping the SAME workload in a transient scope flattens the curve to zero slope

Same fixture, same command, with the loop split into 1,000 batches, each
bracketed by the runtime's existing scope primitives (`extern fn
rt_transient_array_scope_begin() -> bool` / `rt_transient_array_scope_end() ->
bool`; both returned `true` on the first batch, printed to prove the scope
really opened):

| allocations | max RSS (KiB), unscoped | max RSS (KiB), scoped |
|---:|---:|---:|
| 1,000,000 | 84,780 | 38,252 |
| 4,000,000 | 225,484 | 38,284 |
| 8,000,000 | 412,848 | 38,588 |
| 16,000,000 | (not run; ~810,000 extrapolated at 48 B) | **39,180** |

Scoped marginal cost across 1M -> 16M allocations: **(39,180 - 38,252) KiB /
15,000,000 = 0.063 B/alloc** — 762x below the unscoped 48.0 B/alloc, i.e. flat
inside sampling noise while the input grows 16x. The scoped 38-39 MiB is the
`bin/simple run` floor (the 100,000-allocation unscoped row is 40 MiB).

### 3. What this corrects in this record's §4 (2026-08-17)

§4 concluded the remaining owner is a runtime **representation** change and
scoped the fix as "a new registering `rt_object_new`, a new deep-free kind +
child-word scan, ... a header word [that] shifts every struct field GEP in two
backends". Re-read against current source, that is **not** what the runtime
does today, and §2 above is the counter-measurement:

- `rt_alloc` (`src/runtime/runtime_native.c:5920-5946`) already calls
  `rt_core_transient_raw_register` on **both** the guard-sampled and the plain
  `malloc` path.
- `rt_core_transient_classify` (`src/runtime/runtime_native.c:2045-2052`) probes
  the raw registry **first**, *before* the heap-tag test — so an untagged,
  header-less `rt_alloc` block is classified `RT_CORE_TRANSIENT_RAW` with its
  recorded byte size.
- `rt_transient_heap_promote` already word-scans a RAW node's children
  (`src/runtime/runtime_native.c:2131-2139`) and clears the owned bit on
  survivors (`:2156-2161`).
- `rt_transient_array_scope_end` -> `rt_core_reclaim_transient_raw`
  (`src/runtime/runtime_native.c:1372-1382`, `:1549-1568`) frees every entry
  that still carries `RT_CORE_TRANSIENT_RAW_OWNED_BIT`.

So aggregates are *already* registered, *already* traversable, and *already*
reclaimable — no kind header, no GEP shift, no `rt_object_new`. The
`SECOND LIMIT` note (`src/runtime/runtime_native.c:6548-6565`) is accurate about
`rt_core_deep_free_classify`, which is a **different** primitive; it is not the
constraint on the transient path, and §4 read across the two.

### 4. The actual retention, with file:line

`src/runtime/runtime_native.c:1502`

```c
static int rt_core_transient_raw_register_state(void* ptr, size_t bytes, int owned) {
    if (!ptr || !rt_core_transient_array_scope_active) return ptr != NULL;
```

**An allocation made while no transient scope is active is never recorded, so it
can never be freed** — there is no registry entry, no header, and no other
free path for a bare `rt_alloc` block. That single early return is what §1
measures at 48 B/instance and what §2 removes. Reclamation is therefore a
question of *scope coverage over the phase*, not of object representation.

In the Stage-3 streaming HIR phase, the scope covers exactly
`CompilerDriver.lower_streaming_surface_source`
(`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:65-100`): begin ->
`parse_full_frontend` -> `lower_parser_module_unstub` -> pause -> promote HIR +
diagnostics + flat rows + frontend registries -> end. Everything else executed
per source in `lower_and_check_streaming_surfaces_impl` is **outside** any
scope, including `lowering.begin_module(source.path)` (`:254`, which reallocates
~20 dicts/arrays and drops the previous module's), the surface
identity/fingerprint comparisons and their interpolated text (`:213-243`), the
HIR cache key and cached-module path (`:242-274`), the per-module progress and
`log_phase` receipts (`:255-260`), and the post-lowering diagnostic projection
loop (`:294-...`). Each of those allocations is permanently unreclaimable by
construction.

### 5. Seed-interpreted full-closure control (discriminator, NOT a Stage-3 number)

To separate "a Simple-source data structure is retained per module" from "the
runtime cannot free what the source correctly dropped", the same pure-Simple
compiler source was driven under the **Rust seed interpreter**, which has its
own value lifecycle:

```bash
./bin/simple run src/app/cli/bootstrap_main.spl compile --format=smf \
    src/app/cli/bootstrap_main.spl -o out.smf
# sampled every 2s: VmRSS / VmHWM from /proc/<pid>/status,
# joined to the driver's own `[build] <phase> N/775 ... +Tms` progress lines
```

`bootstrap_main.spl` itself drops to the interpreter under the seed
(`[jit-fallback] ... case KwMod:`), so this run exercises the compiler's HIR
lowering **source** without the no-GC native runtime underneath it.

Entry closure: **775 sources** (`source_closure 775/775 ... complete` at
`+23,143 ms`). Process floor before the closure walk: **3,356,704 KiB**.

Parse phase, linear and shallow:

| parse module | VmRSS (KiB) | MiB above floor | MiB/module |
|---:|---:|---:|---:|
| 0 | 3,356,704 | 0 | — |
| 101 | 3,631,876 | 268.7 | 2.66 |
| 239 | 3,924,160 | 554.2 | 2.32 |
| 313 | 4,076,252 | 702.7 | 2.25 |
| 364 | 4,179,828 | 803.8 | 2.21 |


### 6. AMENDMENT — the same measurement on `runtime_native.c` itself (the Stage-3 runtime), plus three corrections to §1-§5

**Correction A (runtime identity).** §1 and §2 ran on `bin/simple`, which is the
Rust seed and therefore links the **Rust twin** of the runtime
(`rt_transient_array_scope_begin` is defined at
`src/compiler_rust/runtime/src/value/collections.rs:1786`), not the
`core-c-bootstrap` `runtime_native.c` that Stage 3 links. Every file:line in §3
and §4 is `runtime_native.c`. That gap is now **closed by direct measurement**
rather than by assuming the twins agree.

A 33-line C fixture declares only the three symbols it uses
(`rt_alloc`, `rt_transient_array_scope_begin`, `rt_transient_array_scope_end`),
allocates `rt_alloc(32)` in batches of 4,000 and writes 4 words into each block,
optionally bracketing each batch with begin/end. It is linked directly against
`src/runtime/runtime_native.c` plus abort-on-call stubs for the 28 unrelated
`spl_*` / `rt_process_*` / `rt_simd_*` symbols the translation unit references
(none is on the allocation path; each aborts if reached):

```bash
~/dev/llvm/install/bin/clang -O2 -o probe main.c stubs.c \
    src/runtime/runtime_native.c -lm -lpthread          # exit 0
/usr/bin/time -v ./probe <N> <0|1>
```

| rt_alloc(32) calls | max RSS, no scope (KiB) | max RSS, scoped (KiB) |
|---:|---:|---:|
| 1,000,000 | 48,556 | **1,816** |
| 4,000,000 | 189,016 | **1,816** |
| 8,000,000 | 376,544 | **1,816** |
| 16,000,000 | 751,416 | **1,816** |

Unscoped marginal cost: `(751,416 - 48,556) KiB / 15,000,000 = ` **47.98
B/alloc** — within 0.1% of the 48.03 B/alloc measured through the Simple/JIT
lane in §1, so the two runtime twins agree. Scoped: **byte-identical 1,816 KiB
at every N**, i.e. a slope of exactly zero over a 16x input range, and the
reclaim is total rather than merely bounded.

This is the Stage-3 runtime, measured, not inferred. §3's conclusion stands on
`runtime_native.c` directly: no kind header, no `rt_object_new`, and no GEP
shift are needed for an `rt_alloc` block to be reclaimed — the existing
transient scope already reclaims 100% of them.

**Correction B (§3 overstated "corrects").** §4 of 2026-08-17 already cited
`rt_core_transient_raw_register`'s scope-gated behaviour. What this lane adds is
not that the earlier reading missed registration, but a measurement showing the
gate is the whole story: the fix is **narrowed** from object representation to
**scope coverage**. Read §3 as narrowing §4, not as refuting it.

**Correction C (§5 mis-described its own lane).** §5 called the seed-interpreted
closure run a discriminator "without the no-GC native runtime underneath it".
That is **false**. `grep -c 'falling back to interpreter'` over that run's log
returns **1**, and the only module named is `src/app/cli/bootstrap_main.spl`
itself — the entire compiler import closure, including `80.driver` and
`20.hir`, is **JIT-compiled** and runs on the seed's runtime with `rt_alloc` and
the transient-scope machinery live. So §5's parse-phase slope (2.2-2.7
MiB/module over 775 sources) is not an interpreter control; it is a *near-repro*
of Stage 3's execution model on a different runtime twin. Treat its slopes as
indicative and its absolute RSS as not comparable to the Stage-3 figures.

**What is still NOT located, stated plainly.** This lane measured the
*mechanism* (an allocation outside a transient scope is unreclaimable, at 48
B/block) and the *scope boundary* in the Stage-3 streaming driver
(`lower_streaming_surface_source` only). It did **not** locate where the
Restart-12 ~63 MiB/module actually lands. The candidates remain open and
unranked: the promoted HIR graph itself, allocations made while the scope is
*paused* (`rt_core_transient_raw_register` records those with the owned bit
clear, so `rt_core_reclaim_transient_raw` skips them —
`src/runtime/runtime_native.c:1512-1514`, `:1553`), the pre-HIR streaming
**surface** phase, or the per-source loop body outside the scope. The loop-body
allocations named in §4 are kilobytes per module by inspection and cannot by
themselves be 63 MiB; §4 names them as *unreclaimable by construction*, not as
the measured owner. This record has a history of confident owner claims that
turned out to be small terms — this is not another one.

**Smallest correct fix (proposed, NOT implemented, NOT measured).** Widen the
per-source transient scope in
`CompilerDriver.lower_and_check_streaming_surfaces_impl` from
`lower_streaming_surface_source` alone
(`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:65-100`) to the whole
loop-body iteration, promoting the small set of values that must outlive it
(the `HirModule` is already promoted; the `CompileContext` diagnostics and
poison markers are not). That is a `80.driver`-owned change, not a
runtime-or-backend one, and is materially cheaper than §4's scoped fix. It must
not be landed on this evidence alone: the correct next step is an instrumented
canonical Stage-3 transaction that reports, per module, promoted bytes vs.
reclaimed bytes vs. RSS delta — which is what would actually rank the four
candidates above. That transaction cannot run in this worktree (no Stage 2, no
Stage 3, and the sanctioned bootstrap was explicitly out of scope for this
lane), so the row stays **OPEN**.

### 7. MEASURED: the PAUSED window inside the Stage-3 HIR scope leaks at the full 48 B/alloc while the active window is reclaimed 100%

Candidate 2 of §6's unranked list is no longer speculation. A second C fixture
replays the driver's exact sequence from
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:65-100` —
`begin` -> allocate (the parse + lower window) -> `pause` -> allocate (the
promotion window) -> `end` — linked the same way against
`src/runtime/runtime_native.c`:

```bash
~/dev/llvm/install/bin/clang -O2 -o probe2 main2.c stubs.c \
    src/runtime/runtime_native.c -lm -lpthread
/usr/bin/time -v ./probe2 4000 4000 <paused_per_batch>
```

Every row performs the **same 16,000,000 active allocations** (4,000 batches x
4,000) and differs only in how many blocks are allocated after `pause`:

| paused per batch | total paused allocs | max RSS (KiB) | RSS above the p=0 floor | B per paused alloc |
|---:|---:|---:|---:|---:|
| 0 | 0 | 2,008 | — | — |
| 10 | 40,000 | 3,928 | 1,920 KiB | 49.2 |
| 100 | 400,000 | 20,728 | 18,720 KiB | 47.9 |
| 1,000 | 4,000,000 | 189,528 | 187,520 KiB | **48.0** |

The 16M **active** allocations cost 2,008 KiB in every row — fully reclaimed.
The **paused** allocations cost **48.0 B each, permanently**, the identical
slope §6 measured for an allocation made with no scope at all. Mechanism, in
source: `rt_core_transient_raw_register` passes
`owned = !rt_core_transient_array_scope_paused`
(`src/runtime/runtime_native.c:1512-1514`), and
`rt_core_reclaim_transient_raw` frees only entries carrying
`RT_CORE_TRANSIENT_RAW_OWNED_BIT` (`:1553`). A paused-window block is recorded,
then skipped by the reclaim, then erased from the table by
`rt_core_transient_raw_clear` (`:1567`) — leaked *and* untracked.

**What executes inside that window on Stage 3.** Between
`rt_transient_array_scope_pause()`
(`driver_hir_pipeline_lowering.spl:75`) and
`driver_end_transient_parse_scope()` (`:98`) the driver runs four promotion
walkers: `rt_transient_heap_promote(hir_module)` (`:79`),
`lowering.promote_diagnostics_transient_owner()` (`:83`, itself three more
`rt_transient_heap_promote` calls — `src/compiler/20.hir/hir_lowering/types.spl:564-571`),
`bootstrap_hir_modules_promote_last()` (`:90`), and
`driver_promote_frontend_registry_owners()` (`:94`). Every `rt_alloc` any of
those makes is retained for the life of the process.

**Arithmetic bridge to Restart-12, stated as a hypothesis with its own falsifier.**
63 MiB/module / 48 B = **~1.38 million leaked blocks per module**. The
2026-08-22 instrumentation measured **38,060 promoted nodes** for module 1, so
this window would have to allocate ~36 blocks per promoted node to account for
the whole slope. That is a *testable* number, not a conclusion: it is refuted if
an instrumented Stage 3 shows the paused window allocating materially fewer than
~1.4M blocks per module, in which case the remaining candidates from §6 (the
promoted graph itself, the pre-HIR surface phase, the unscoped loop body) carry
the balance. **No Stage-3 run was made in this lane, so the bridge is unverified
and must not be quoted as the located owner.**

**How to test it cheaply on the next Stage 3.** `rt_core_transient_raw_register_state`
already sees every block and already knows the paused flag; a counter pair
(blocks and bytes registered with the owned bit clear, per scope) reported
alongside the existing `hir-promotion` / `hir-promotion-total` snapshot rows
would settle the attribution in one transaction, with no representation change
and no behaviour change.

### 8. Closure-scale control, and one lane that died

Non-streaming full closure (775 sources, `src/app/cli/bootstrap_main.spl`),
seed JIT, parse phase, VmRSS joined to the driver's own progress lines:

| parse module | VmRSS (KiB) |
|---:|---:|
| 0 | 3,412,876 |
| 160 | 3,737,276 |
| 320 | 4,096,484 |
| 480 | 4,512,004 |
| 640 | 4,824,028 |
| 688 | 4,929,612 |

Linear at **2,204 KiB/module** over 688 modules (segment slopes 2,136 and 2,264
KiB/module), i.e. ~2.15 MiB/module — three orders of magnitude below the
Restart-12 HIR-phase 63 MiB/module, so the parse phase is not the shape this
P0 is about.

That run was **SIGKILLed (rc=137) at parse 688/775, 4,929,612 KiB**, on a shared
box where 83 of 121 GiB were held by other agents' processes at the time (101
GiB free immediately after). It is recorded as a truncated run, not as a
reproduction of this bug's termination: the record's own 2026-08-14 warning
applies — a kill without a monotonic HIR-phase RSS trace is not a repro.

### 9. Appendix — the two C fixtures, verbatim, so the numbers can be re-run

Both link the same way. `stubs.c` defines the 28 unrelated `spl_*` /
`rt_process_*` / `rt_simd_*` / `rt_getcwd` / `rt_is_dir` / `rt_dir_remove_all` /
`rt_sleep_ms_native` / `rt_text_slice_audit_*` symbols the translation unit
references as `void name(void) { abort(); }` — none is on the allocation path,
and any call aborts loudly rather than being silently absent:

```bash
~/dev/llvm/install/bin/clang -O2 -o probe main.c stubs.c \
    src/runtime/runtime_native.c -lm -lpthread
```

`main.c` (§6 — scope vs no scope; `./probe <N> <0|1>`):

```c
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

void*  rt_alloc(int64_t size);
int8_t rt_transient_array_scope_begin(void);
int8_t rt_transient_array_scope_end(void);

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage: probe N SCOPED\n"); return 1; }
    long n = atol(argv[1]);
    int scoped = atoi(argv[2]);
    long batch = 4000;
    long done = 0;
    volatile long sink = 0;
    while (done < n) {
        long take = (n - done) < batch ? (n - done) : batch;
        if (scoped) {
            if (!rt_transient_array_scope_begin()) { fprintf(stderr, "begin failed\n"); return 2; }
        }
        for (long i = 0; i < take; i++) {
            int64_t* p = (int64_t*)rt_alloc(32);
            if (!p) { fprintf(stderr, "alloc failed\n"); return 3; }
            p[0] = i; p[1] = i; p[2] = i; p[3] = i;
            sink += p[0];
        }
        if (scoped) {
            if (!rt_transient_array_scope_end()) { fprintf(stderr, "end failed\n"); return 4; }
        }
        done += take;
    }
    printf("n=%ld scoped=%d sink=%ld\n", n, scoped, (long)sink);
    return 0;
}
```

`main2.c` (§7 — active window vs paused window; `./probe2 4000 4000 <paused>`):

```c
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

void*  rt_alloc(int64_t size);
int8_t rt_transient_array_scope_begin(void);
int8_t rt_transient_array_scope_pause(void);
int8_t rt_transient_array_scope_end(void);

/* Replays the Stage-3 driver's sequence in lower_streaming_surface_source:
   begin -> allocate (parse + lower) -> pause -> allocate (promotion-time work)
   -> end. ACTIVE blocks are registered owned; PAUSED blocks are registered with
   the owned bit clear, so rt_core_reclaim_transient_raw skips them. */
int main(int argc, char** argv) {
    if (argc < 4) { fprintf(stderr, "usage: probe2 BATCHES ACTIVE PAUSED\n"); return 1; }
    long batches = atol(argv[1]);
    long active  = atol(argv[2]);
    long paused  = atol(argv[3]);
    volatile long sink = 0;
    for (long b = 0; b < batches; b++) {
        if (!rt_transient_array_scope_begin()) { fprintf(stderr, "begin failed at %ld\n", b); return 2; }
        for (long i = 0; i < active; i++) {
            int64_t* p = (int64_t*)rt_alloc(32);
            if (!p) return 3;
            p[0] = i; sink += p[0];
        }
        if (!rt_transient_array_scope_pause()) { fprintf(stderr, "pause failed\n"); return 4; }
        for (long i = 0; i < paused; i++) {
            int64_t* p = (int64_t*)rt_alloc(32);
            if (!p) return 5;
            p[0] = i; sink += p[0];
        }
        if (!rt_transient_array_scope_end()) { fprintf(stderr, "end failed\n"); return 6; }
    }
    printf("batches=%ld active=%ld paused=%ld sink=%ld\n", batches, active, paused, (long)sink);
    return 0;
}
```

The Simple-lane fixtures of §1/§2 are the `Node` / `Node8` / `[i64]` loops
already quoted there; the scoped variant wraps each 1/1000th of the loop in
`extern fn rt_transient_array_scope_begin() -> bool` /
`rt_transient_array_scope_end() -> bool` and prints both return values on the
first batch, so a silently-refused scope cannot be mistaken for a flat curve.

### 10. Refinement to §7's bridge — the paused window is REAL but probably SMALL; the likelier owner is what promotion un-owns

§7's mechanism (a paused-window `rt_alloc` leaks at 48.0 B, measured) stands.
Its *arithmetic bridge* to 63 MiB/module does not survive inspection of what
actually runs in that window, and this is recorded now rather than left for the
next session to chase:

- `driver_promote_frontend_registry_owners`
  (`src/compiler/80.driver/driver_source_pipeline_parsing.spl:248-253`) is four
  calls to `*_promote_transient_owner()` and an `and` — no Simple-side
  allocation of consequence.
- `HirLowering.promote_diagnostics_transient_owner`
  (`src/compiler/20.hir/hir_lowering/types.spl:564-571`) is three
  `rt_transient_heap_promote` calls and an `and` — likewise.
- `rt_transient_heap_promote` itself allocates its plan/seen arrays with
  `calloc`/`realloc` and `free`s both before returning
  (`src/runtime/runtime_native.c:2164-2165`), so it does not go through
  `rt_alloc` at all and cannot leak through the paused registry.

So the paused window on Stage 3 probably allocates hundreds of blocks per
module, not ~1.4 million. **§7's bridge is therefore unlikely, and should be
treated as refuted-pending-measurement rather than as a lead.** The measured
mechanism remains worth fixing (it is an unbounded leak with no upper bound in
the code), but it is not the 63 MiB.

**The candidate this promotes to first place instead.** `rt_transient_heap_promote`
clears the owned bit on *every* node it reaches
(`src/runtime/runtime_native.c:2141-2162`), and for a `RT_CORE_TRANSIENT_RAW`
node it enumerates children by scanning **every 8-byte word of the block** and
calling `rt_core_transient_add` on each (`:2131-2139`). Two consequences:

1. Everything transitively reachable from the promoted HIR module survives the
   scope end by design — so the per-module retained cost is the *closure* of the
   HIR graph, not the HIR graph. If any HIR node still points into the
   `ParserModule`/AST or into per-module lowering scratch, the whole of it is
   retained, and `ast_reset()` at `driver_hir_pipeline_lowering.spl:427` (which
   runs once after the loop, not per source) cannot give it back.
2. The word scan is untyped. Any i64 field whose value happens to collide with a
   live registered pointer is followed, and whatever it reaches is un-owned too.
   That is a *conservative* retention path with no bound stated anywhere in the
   runtime.

Neither is measured here. What distinguishes them from §7's bridge is that the
2026-08-22 instrumentation already reports exactly the number that would settle
it — `hir-promotion-total` promoted **38,060 nodes / 1,218,945 bytes** for
module 1, i.e. ~1.2 MB against an RSS of 640,932 KiB at that point. If the next
Stage 3 shows promoted bytes staying near 1.2 MB per module while RSS climbs 63
MiB per module, promotion is *not* the owner either and the remaining candidate
is the pre-HIR streaming surface phase. If promoted bytes track the RSS slope,
it is.

**Revised cheapest next test** (supersedes §7's, same spirit, one extra counter):
report, per source, (a) blocks/bytes registered while the scope was PAUSED,
(b) blocks/bytes un-owned by promotion, and (c) blocks/bytes actually freed by
`rt_core_reclaim_transient_raw`, beside the existing `hir-promotion` /
`hir-promotion-total` rows. All three are already visible inside
`rt_core_transient_raw_register_state`, `rt_transient_heap_promote` and
`rt_core_reclaim_transient_raw`; none requires a representation or behaviour
change. Those three numbers plus RSS rank all four candidates in a single
transaction.

**§6's proposed fix is withdrawn as a fix.** Widening the per-source transient
scope to the whole loop-body iteration remains a correct repair for the
*measured* mechanism (§6's unscoped blocks, §7's paused-window blocks), and is
still worth doing on its own terms. It cannot address the promotion-closure
candidate: everything transitively reachable from `hir_module` is un-owned by
`rt_transient_heap_promote` regardless of where the scope boundary is drawn, so
if that closure is the owner, widening the scope reclaims nothing additional.
Do not land it as this P0's fix on the strength of §6 alone.
