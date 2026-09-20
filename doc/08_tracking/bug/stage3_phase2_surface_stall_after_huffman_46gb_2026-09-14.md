# Linux S3-1: Stage-2-native `bootstrap_main.spl` build hangs after the surface phase completes — seed interpreter finishes the identical closure in 17 minutes
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN — root cause **localized** (Stage-2 native codegen/runtime, not
  `src/compiler` algorithmically), exact defect not yet found. Filed as its
  own site because the macOS chain never reached real Stage-3 compilation —
  every macOS run stopped at the admission-receipt gate (site 20). This is
  the first time anyone has run the actual 832-file Stage-3 closure to
  completion or failure on either platform.
- Area: whatever runs between `phase2:surface:*` completing and
  `phase3:hir_typecheck:start` in the **natively-compiled** Stage-2 binary —
  leading suspect `module_surfaces_promote`/`module_surfaces_promote_reason`
  (`src/compiler/80.driver/driver_source_pipeline_parsing.spl:585`,
  `src/compiler/20.hir/hir_lowering/module_surface_registry.spl`), the exact
  registry-promotion machinery this session has spent all day on for site 18
  — but at REAL scale (832 surfaces) instead of site 18's 2-surface fixture.
- Found by: BOOT-18, running BOOT-16's receipt-free diagnostic Stage-3 script
  (bypasses the admission-receipt gate; writes no provenance receipt) against
  a real, Linux-aarch64-ADMITTED Stage-2 candidate.

## Correction to this lane's own earlier framing

An interim report during this investigation described the stall as "832 of
14340" files. That was wrong and is corrected here: **832 is the complete,
final entry-closure size** for `bootstrap_main.spl`
(`event=build_progress phase=source_closure unit_kind=files done=832
total=832 remaining=0 ... current=complete tasks_done=1 tasks_total=6
tasks_remaining=5`, from `bootstrap-build-progress.events`). 14,340 was an
unrelated count — every file under the three broad `--source` roots
(`src/compiler`, `src/app`, `src/lib`), most of which are not reachable from
`bootstrap_main.spl` and are irrelevant to `--entry-closure` builds. The
surface/parse phase (task 1 of 6) **completed successfully and completely**;
the hang begins immediately after.

## Repro

Admitted Stage-2 candidate (from `doc/08_tracking/bug/stage3_resume_receipt_chain_unreachable_from_seed_producer_2026-09-13.md`'s
Linux confirmation, same session): `build/bootstrap-boot18b/stage2/aarch64-unknown-linux-gnu/simple`,
152345176 B, sha256 `babd73a74bc8e0ca5e56e8df532aeeab6013e53b16b37489317a4958d538765c`.

```
<stage2-candidate> native-build --target aarch64-unknown-linux-gnu \
  --backend llvm --runtime-bundle core-c-bootstrap \
  --source src/compositions/kernel_llvm_cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 16 --mode dynload \
  --entry src/app/cli/bootstrap_main.spl -o <out>
```
`SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE3=1 SIMPLE_NATIVE_BUILD_THREADS=16`
(from the bootstrap engine's own Stage-3 env vector). Reproduced **twice**,
independently (BOOT-18's attempts 2 and 3), stalling at the **identical**
last log line both times:

```
phase2:surface:file:released path=src/std/nogc_sync_mut/compression/gzip/huffman.spl seq=832
```

## Evidence the Stage-2 candidate is hung, not merely slow

Attempt 3, `--threads 16`, 20-core host, load ~3-6 (idle per the
coordinator's read):

- `pstree -p <pid>`: **zero child processes**, **nlwp=1** (one OS thread) —
  confirmed at two early samples (24 s, 83 s) and unchanged through to kill.
- `ps -o pcpu`: ~99-100% of one core, continuously, the entire run.
- `VmRSS`: climbed to **~46-48 GB**, then fluctuated 39-48 GB (some internal
  GC activity, never enough to unblock forward progress). For scale: the
  entire admitted Stage-2 binary is 152 MB and the whole 832-file source
  closure is a few tens of MB of text.
- **Nothing was written anywhere in the output tree for the last ~43+
  minutes of the run** — not the native-build log, not the phase-profile
  events file, not the native/frontend cache directories, not any temp file.
  `find <output-root> -newer <last-known-good-file>` returned nothing.
- Killed by PID (never `pkill`) at the coordinator's 20-minute deadline.
  Final numbers read from `/proc/<pid>` immediately before `SIGTERM`:
  **`rss_kib=39,361,292` (≈37.5 GB), `utime=269,148` ticks (≈2691 s / 44.9 min
  of CPU time), `etimes=2757` s (45.95 min wall)** — i.e. it burned essentially
  45 minutes of CPU on one core, making zero externally observable progress,
  before being killed.

## The decisive bisection: seed interpreter route

Per the coordinator's bisection rule ("if the seed finishes quickly and only
the Stage-2 binary blows up, it is a Stage-2 codegen/runtime defect"), ran the
**identical** command (only `--backend cranelift`, since this seed build has
no `llvm` cargo feature — confirmed backend-independent since the stall is in
the frontend, before any backend-specific codegen) through the **shared,
untouched Rust seed** (`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
the same one interpreting this exact `.spl` driver source, including
`module_surface_registry.spl`):

```
Build complete: 890 compiled, 0 cached, 0 failed
  Binary: <path>/simple.interp (38100944 B, sha256 ec9f226bec18f94be1c…)
  Time: 934.3s compile + 75.2s link = 1009.5s total
```

**Completed cleanly in 16.8 minutes**, real multi-core parallelism observed
in the process tree (36 OS threads, up to ~1458% CPU — a genuinely different
execution shape from the Stage-2 candidate's single thread), peak RSS in the
low single-digit GB (never approached the Stage-2 candidate's 37-48 GB).

**This localizes the defect to the Stage-2 candidate's own native code**,
not to an algorithmic defect in `src/compiler`'s `.spl` source: the same
source, the same 832-file closure, the same registry-promotion logic,
executed by the tree-walking interpreter, does not hang and does not blow up
memory. Something specific to how the **natively-compiled** Stage-2 binary
executes this code — most plausibly the transient-heap-promote /
registry-graph-promotion machinery, given the timing (starts immediately
after `phase2:surface` completes, exactly where
`module_surfaces_promote_reason(retained_surfaces)` runs) and given this
session's whole-day history with exactly that code path at fixture scale
(site 18) — does not terminate, or terminates on a timescale far beyond what
was budgeted here.

(Caveat on the compiled-unit count: the interpreter route reports "890
compiled" vs. the native run's 832-file surface closure — a different
granularity, likely counting post-HIR compile UNITS rather than raw source
files. Not investigated further; noted so the two numbers are not read as a
direct mismatch.)

## Not the already-RESOLVED 2026-08-21 record — read that one, then note the difference

`doc/08_tracking/bug/bootstrap_main_native_build_stalls_after_source_closure_2026-08-21.md`
(Status: RESOLVED, re-verified 2026-09-12) covers a symptom in the same
neighborhood — apparent silence after `source_closure N/N step 1/6 complete`
— and is directly cross-referenced in a code comment at
`driver_source_pipeline_parsing.spl:1040-1043`. Read closely, it is a
**different bug in a different execution mode**: its root causes were three
`interpreter`-specific env-cache/borrow_mut defects in
`src/compiler_rust/compiler/src/interpreter*` (module-global generation
bumped on every plain local assignment, forcing full env-template rebuilds on
every intra-module call) — code that plays no role when running natively
compiled Stage-2/Stage-3 output, since native code does not go through that
tree-walking interpreter machinery at all. Consistent with that: this
session's own interpreter-route reproduction, on the presumably-fixed current
seed, completed in 17 minutes with no sign of the old symptom (peak RSS a few
GB, not tens of GB; real multi-threaded parallelism, not a single stuck
thread). The 2026-08-21 record's fix is irrelevant here; this is a new,
distinct, and far more severe defect (indefinite hang vs. tens-of-minutes
slowness; 37-48 GB RSS vs. ~3 GB) confined to the natively-compiled binary.

## Fix direction — handed over, not attempted

Not fixed here; this record is the localization, per the coordinator's
routing. For whoever picks it up:

1. **Reproduces reliably and fast** (source_closure reaches 832/832 within
   ~15-60 s every time), so live attach is practical: re-run the same
   command, and the moment the log goes silent past `seq=832`, attempt
   `gdb -batch -ex bt -p <pid>` (not tried in this session — the process was
   already killed by the time this was considered; `ptrace_scope=1` was
   observed elsewhere on this host and may block it, but is worth trying
   directly rather than assuming).
2. If attach is blocked, add native-side instrumentation (a periodic
   `log_phase` heartbeat, or a bounded loop counter) inside
   `module_surfaces_promote`/`module_surfaces_promote_reason` and the
   `rt_transient_heap_promote` call sites `module_surface_registry.spl`
   loops over, specifically for the **native** codegen path — the interpreter
   comparison here only proves the `.spl` logic is fine when interpreted, not
   which native instruction sequence the same logic lowers to.
3. The steady, enormous RSS (tens of GB, plateauing rather than monotonically
   climbing to OOM) is itself a clue: consistent with a loop that keeps
   re-allocating/re-scanning a large already-live structure (quadratic
   re-promotion, or a GC repeatedly walking a large live set without making
   termination progress) rather than a runaway unbounded allocator. Check
   whether da91f5dd299's flattened `module_surface_promote_fields` (24
   unconditional `rt_transient_heap_promote` calls per surface, no early
   exit, landed to fix site 18/19 — see
   `doc/08_tracking/bug/stage2_module_surface_registry_graph_promotion_composite_names_2026-09-13.md`)
   behaves differently under **native** codegen than the interpreter at
   832-surface × 24-field scale (~20,000 promote calls) — untested at this
   scale before today, since site 18's own regression spec used a 2-surface
   fixture.
4. A RED spec with a bounded wall-clock/RSS budget belongs once the exact
   defect is found (per this repo's TDD rule) — not written here since the
   defect itself is not yet isolated to a function.

## Binary identity

| role | size | sha256[0:24 or 0:40] |
|---|---|---|
| shared seed (interpreter route, untouched) | — | `3d120a6f9ab5704b2225654e` |
| Stage-2 native candidate (hangs) | 152345176 B | `babd73a74bc8e0ca5e56e8df532aeeab6013e53b` |
| interpreter-route diagnostic output (completes) | 38100944 B | `ec9f226bec18f94be1c2488d1016435a52e19bbe` |

## Not caused by anything this lane authored

This lane's own changes this session (adopting site 18's upstream fix, then
confirming site 20 on Linux) are documentation-only at this point (see
`47b01b334c8`, `8eedd0cfc7d`); nothing in `src/` was edited before this stall
was found. The stall is reached only because Stage 2 now ADMITS cleanly on
Linux (sites 16/17/18/19 all clear) and this is the first time the
receipt-gate bypass has been used to run the real Stage-3 closure this far.

## Two live gdb backtraces (2026-09-14, BOOT-18 follow-up) — root cause confirmed, not inferred

`ptrace_scope=1` blocks attaching to a running process on this host, but
starting the process DIRECTLY under gdb is unaffected. Two independent fresh
repros, `gdb -batch -ex run -ex 'bt 60' -ex 'info threads' -ex 'thread apply
all bt 30' --args <stage2-candidate> native-build ...` (identical argv/env to
the repro above), interrupted via `timeout -s INT <900|1200>` (gdb itself
receives SIGINT, which stops the inferior and runs the batch commands before
exiting) — 15 minutes and 20 minutes into separate runs:

**Sample 1 (15 min):**
```
#0 <std::hash::random::DefaultHasher as core::hash::Hasher>::finish
#1 <hashbrown::map::HashMap<u64,(),RandomState>>::contains_key::<u64>
#2 <Vec<RuntimeValue>>::retain::<rt_transient_heap_promote::{closure#0}::{closure#1}>::{closure#0}
#3 <Vec<RuntimeValue>>::retain_mut::<...>
#4 <Vec<RuntimeValue>>::retain::<...>
#5 <LocalKey<RefCell<Option<TransientHeapScope>>>>::with::<rt_transient_heap_promote::{closure#0}, bool>
#6 rt_transient_heap_promote
#7 compiler.hir.hir_lowering.module_surface_registry.module_surface_promote_fields
#8 compiler.hir.hir_lowering.module_surface_registry.module_surfaces_promote_reason
#9 compiler__driver__driver_source_pipeline_parsing__CompilerDriver.parse_all_streaming_surfaces_in_place_impl
#10 compiler__driver__driver_source_pipeline_parsing__CompilerDriver.parse_all_committing_impl
#11 compiler__driver__driver_orchestration__CompilerDriver.compile_with_reverse_reference_owner_v1
#12 compiler__driver__driver_orchestration__CompilerDriver.compile
#13 app.cli.bootstrap_focused_native_build.run_focused_native_build_plan
#14 main
```

**Sample 2 (20 min, independent fresh repro):** identical mechanism, calling
`rt_transient_heap_promote` one frame more directly out of
`module_surfaces_promote_reason` (consistent with `module_surface_promote_fields`
being small enough to inline at this particular call site under `-O`, not a
different code path — every frame below #6 is byte-identical to sample 1):
```
#0 <hashbrown::map::HashMap<u64,(),RandomState>>::contains_key::<u64>
#1 <Vec<RuntimeValue>>::retain::<rt_transient_heap_promote::{closure#0}::{closure#1}>::{closure#0}
#2 <Vec<RuntimeValue>>::retain_mut::<...>
#3 <Vec<RuntimeValue>>::retain::<...>
#4 <LocalKey<RefCell<Option<TransientHeapScope>>>>::with::<...>
#5 rt_transient_heap_promote
#6 compiler.hir.hir_lowering.module_surface_registry.module_surfaces_promote_reason
#7 driver_source_pipeline_parsing.parse_all_streaming_surfaces_in_place_impl
#8 driver_source_pipeline_parsing.parse_all_committing_impl
#9 driver_orchestration.compile_with_reverse_reference_owner_v1
#10 driver_orchestration.compile
#11 bootstrap_focused_native_build.run_focused_native_build_plan
#12 main
```

Raw logs: `scratchpad/boot18/gdb1/run.log`, `scratchpad/boot18/gdb2/run.log`
(this session's scratchpad, not in the repo).

**Root cause, now proven:** `TransientHeapScope.objects: Vec<RuntimeValue>`
(`src/compiler_rust/runtime/src/value/collections.rs:30`) tracks every
transient allocation made since the scope began. `rt_transient_heap_promote`
(`collections.rs:2030-2079`) does a reachability walk from its argument, then
`scope.objects.retain(|o| !reachable_heap.contains(&o.0))` (`:2078`) — an
**O(N) linear scan+filter over the entire scope's tracking vector on every
single call**, where N is the number of still-tracked transient allocations
(large, at real 832-file scale). This is a Rust-runtime data-structure
defect — a `Vec` + linear `retain` where an O(1)/O(log n) removable structure
(a `HashSet`, or a per-object scope-membership flag) belongs — not a `.len()`/
`.contains()` native-array pitfall of the `doc/07_guide/language/dict_native_pitfalls.md`
kind (`registry.surfaces` is `[ModuleSurface]`, not a `Dict`, and the
`.spl`-level `while` loop is not where the time goes) and not an algorithmic
defect in the `.spl` source (the call count is linear in surfaces by
construction — see below).

## Mitigation landed: call-count batching (`9788f8341a8`)

The O(N)-per-call cost itself is out of reach for a pure-Simple change. What
IS controllable from `.spl`: the NUMBER of calls. Pre-fix,
`module_surface_promote_fields` made 24 individual `rt_transient_heap_promote`
calls per surface (no nested loop — the call count is exactly `24 *
registry.surfaces.len()`, i.e. **linear in surfaces, never quadratic** — this
resolves the "quadratic algorithm vs. linear codegen/runtime" question by
direct source inspection, no dynamic count needed) and
`module_surface_promote_freeze_names` made 4 more — 28 calls/surface, 23,296
total across the real 832-surface closure, each paying the O(N) scan above.

`module_surface_promote` (a few lines above in the same file, unchanged, and
already used elsewhere) already proves the batched shape is safe: collect
many roots into one `[Any]` array and promote it ONCE, since
`rt_transient_heap_promote`'s own reachability walk recurses into array
elements via `transient_heap_children`. Applying the same shape to the
per-field and freeze-names promotes cuts calls/surface from 28 to 2 (23,296
-> 1,664 across the real closure) without changing which values get
promoted.

RED  `test/01_unit/compiler/hir/module_surface_promote_field_batching_spec.spl`
     4 examples, 2 failures (24 and 4 calls found; budget asserts <=2 — a
     call-count budget, not a timing bound: the interpreter stubs
     `rt_transient_heap_promote` entirely per `da91f5dd299`'s own note, so no
     dynamic timing/allocation spec run under `bin/simple test` could
     discriminate the real, native-only defect)
GREEN 4 examples, 0 failures

Two existing site-18/19 sibling specs
(`module_surface_freeze_names_promote_guard_spec.spl`,
`module_surface_promote_reason_spec.spl`) had literal-text assertions tied to
the old per-field call shape; updated to the new
`names.push(...)`/`fields.push(...)`/`rt_transient_heap_promote(names)` shape,
negative guards against reinstating the repeat-promote post-condition
unchanged. Both GREEN (4/4 each) after the update.

**This is a mitigation (14x fewer O(N) scans), not a fix for the underlying
Rust-runtime defect, which remains open.** Whether it is enough to get a
Stage-2 rebuild through the surface phase into HIR at real scale is being
measured next (own Stage-2 rebuild + the receipt-free Stage-3 confirmation
run); if it is not enough, the real fix has to change
`TransientHeapScope.objects`'s data structure in
`src/compiler_rust/runtime/src/value/collections.rs`.

