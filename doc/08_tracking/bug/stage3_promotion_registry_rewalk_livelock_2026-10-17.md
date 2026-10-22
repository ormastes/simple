# Stage3 mono-phase livelock: per-module registry promotion re-walks accumulated dicts (runtime walker)

Date: 2026-10-17
Lane: release_phase3 Windows stage3 direct build (phase-2 binary from the
2026-10-17 admitted lane), entry src/app/cli/bootstrap_main.spl, 1301-module
closure, `--mode dynload`, llvm backend.
Status: ROOT-CAUSED (debugger-verified); fix not yet landed.

## Symptom

The build grinds normally through parse/HIR (~8 min), then mono-lowering's
per-module promotion phase slows to a deterministic crawl: full core for
~15 min (RSS ~13 GB), then CPU collapses to ~3% of one core with RSS
clamped ~25-38 GB, zero paging (Pages/sec = 0, 16 GB free), forever. Not
environmental: reproduces on a freshly-cleaned 44 GB-free box; not the
previous mir-boundary AV (that fix IS in this binary).

## Debugger evidence

cdb attach at the stall, thread 0 (frame RVAs into
.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe;
.pdata-verified against build/phase_snapshots/phase1_1792183153_phase2_1792183827/simple,
md5-identical to the running binary):

```
0xf787b3  runtime predicate leaf (element header test)
0xf75144  runtime retain/filter compaction — iterates bound=[c+0x10],
          predicate per element, move-kept-down, WRITES new length to [c+0x10]
0xf751b7  wrapper
0xfa56b6  runtime container walker 0xfa549d-0xfa570a (data descriptor:
          Rust panic record "valid byte array data layout",
          compiler_rust/runtime/src/value/collections.rs:748/753);
          retry loop 0xfa566e pop->process->jne retry; then retain-filter
0xf6058d  runtime per-root wrapper (20 sequential call sites)
0x4defa8  bootstrap_mir_registries_promote (bootstrap_globals.spl:116-160)
0x560583  lower_module_transient_scoped (module_lowering.spl:1926-1937)
0xc642fd  lower_to_mir_with_target_context  0xbf27cb lower_to_mir
0xc588e8  CompilerDriver.compile ... CLI main
```

## Mechanism (primary hypothesis, evidence-backed)

`lower_module_transient_scoped` runs `bootstrap_mir_registries_promote()`
ONCE PER MODULE (~1300x). That promotes 20 module-global accumulators
(bootstrap_globals.spl:136-155), two of which are Dict<text, text/bool>
(`_bootstrap_callable_link_names`, `_bootstrap_callable_text_value_abi`)
that GROW MONOTONICALLY across all modules (callable links per module).

The runtime promote (0xf60553 -> walker 0xfa549d) re-walks each container's
ELEMENTS on every pass. For a dict, the "elements" are the raw words of the
open-addressing entries array (keys/values/hashes/occupied bytes). The
retain/filter (0xf75105) then writes the kept SLOT COUNT -- including
tombstones -- back into the container's `len` word (+0x10). Each promote
pass therefore INFLATES `len`; the next pass iterates the inflated bound:
geometric explosion to an effective livelock (a ~1e5-entry dict becomes a
~1e18-bound crawl over a handful of per-module passes).

Secondary suspect (same frame region): the walker's retry loop
(0xfa566e) re-enqueues items whose `*object_scope == scope_id` promote
marking fails; a never-draining queue presents identically.

Tertiary: open-addressing `for(;;)` probes (rt_core_transient_seen_insert
runtime_native.c:2673, rt_core_dict_put :10661) spin at 100% table load if
tombstone/live accounting is corrupted by the len write-back.

## Why the previous (crashing) runs did not show it

They access-violated at the (span, symbol) initializer sort in the FIRST
module's mir lowering -- before enough per-module promote passes
accumulated to detonate the dict-len inflation.

## Fix directions (ranked)

1. Runtime walker (collections.rs:693+ / the 0xfa549d walker + 0xf75105
   filter): never iterate a DICT container with the element-array path;
   never write a filtered slot count into `len`. Clamp the iteration bound
   to the validated element count.
2. Call site (bootstrap_globals.spl bootstrap_mir_registries_promote): the
   C promote is documented O(1)-idempotent on already-promoted containers
   via the seen-set; make the skip explicit per root (skip roots whose
   scope tag shows already-promoted) so the walker is not re-entered over
   unchanged accumulated registries. NOTE: takes effect only on a phase-2
   rebuild (same producer-fix discipline as the mir-boundary crash).
3. Defense in depth: probe-iteration cap (fail closed) on the two
   `for(;;)` open-addressing loops (runtime_native.c:2673, :10661).

## Evidence artifacts

- .simple/logs/cdb-livelock2.log (frame addresses), cdb-livelock.log
  (stacks), bootstrap-stage3-newbin*.log (build progression + stall).
- agent-7 .pdata mapping: 20 call sites at 0x4defa8 == 20 registries at
  bootstrap_globals.spl:136-155.

## Fix landed (2026-10-17, work/promotion-rewalk-livelock-20261017)

Fix directions 1 and 3 implemented; direction 2 (call-site skip) skipped
because no per-object promoted/scope-tag predicate is exposed to Simple
(the only accessible transient accessor is the per-THREAD
`rt_transient_array_scope_state_v1`, 0/1/2) and inventing a runtime API
was out of scope.

1. Runtime walker (`src/compiler_rust/runtime/src/value/collections.rs`,
   `transient_heap_children`): the dict arm now validates the
   open-addressing header (`data` non-null, `len <= capacity`,
   `capacity <= 2^32`) BEFORE any slot word is used as an iteration
   bound, and rejects corrupt headers as leaves instead of walking
   garbage; the array arm likewise validates `len <= capacity` before
   slicing. The walker only ever emits occupied (key, value) pairs —
   never slot words as generic elements — and never writes
   `len`/`capacity`/`data`. Regression test
   `dict_promote_rewalk_never_rewrites_len_and_children_survive`
   double-promotes a 200-entry dict (the per-module rewalk shape).
3. Defense in depth (`src/runtime/runtime_native.c`): bounded
   probe-iteration caps (4x table capacity, fail closed with a stderr
   diagnostic) on `rt_core_transient_seen_insert` and
   `rt_core_dict_put`'s open-addressing loops, so corrupted
   accounting turns into a loud failure instead of a `for(;;)` spin.

Note: none of the three lanes' promote walkers (Rust seed, C runtime,
pure-Simple `core_memory.spl`) contained a filtered-slot-count write-back
into a dict `len` in current source — the doc's mechanism was a
disassembly hypothesis. The observed livelock signature (pop-based walker
+ `Vec::retain` frames) is fully explained by the per-module full-graph
re-walk of monotonically growing registry dicts across ~1300 modules on a
multi-GB scope working set. The validation/clamps above fail closed on
the corrupt-header path; the residual quadratic re-walk cost needs either
a per-object promoted predicate (Simple-visible runtime API) or a
single-walk batched promote of all 20 roots — recorded here as follow-up.

## E-LANE-VACUOUS regression attribution (2026-10-17, work/promote-walker-layout-fix)

The stage2 sanity failure (`compiler.bootstrap_admission.p2_add`,
`functions_emitted=0`) was suspected to be the walker validation firing
on a non-RustRuntimeDict layout. Analysis exonerated the guard:

- The sanity binary links the RUST runtime exclusively (rustc panic
  strings present; the C runtime's `[transient-promote] root refused`
  marker and the PR's C probe-cap strings absent), so the C probe-cap
  hunks are not even in the failing binary, and `Dict`/`[i64]` values
  ARE `RuntimeDict`/`RuntimeArray` there.
- `get_typed_ptr`/`heap_type` (heap.rs/core.rs) require BOTH
  Rust-registry membership AND an exact type-tag match, so non-RuntimeDict
  objects take the `None` path in old and new code alike — byte-identical
  behavior; the "layout confusion" path cannot reach the new guards.
- Every Rust-runtime dict/array mutator preserves the guarded invariants
  (grow-before-insert at 3/4 load; typed-words setters bound-check
  against capacity), and promote runs only while the scope is paused, so
  no valid mid-operation state can trip the guards.
- Ordering: in `lower_module_transient_scoped`
  (module_lowering.spl:2000-2023) the emission loop runs BEFORE any
  promote; `functions_emitted` is decided before the walker executes, so
  the walker cannot change it for the module being lowered.
- The in-tree cycle-94/97/98 receipts (module_lowering.spl:2736-2755)
  document this exact vacuity from corrupted key-carried dict draws in
  the compiled host and were fought with the two commits that landed
  after PR #3603 (6d9894da2e0, e6b68a290bf).

Hard follow-up commit on `work/promote-walker-layout-fix`: guard fires
now emit a loud stderr diagnostic (corrupt-header leaf restored for the
benign null-data case to the exact old `Some(vec![])` contract), plus
tests pinning that valid containers (grown boxed arrays, byte/u64-packed
arrays, tuples, grow-boundary dicts) are never dropped and that a
corrupt child is refused without hanging the promote. If the guard ever
fires in a lane, its log line settles attribution immediately.

## Addendum 2026-10-17 (evening): smoke AV persists through upstream p2_add cycles 91-126

Seven lane attempts on the moving tip; the stage2 sanity frontend-smoke AV
(0xC0000005) persisted at cycles 105/112/126 with EVOLVING signatures
(cdb-smoke5/6/7.log):
- cycle-105/112: `mov r9,[rbp]` rbp=0 in prescan_one_function_v1
  (nil prescan_fn via values()/thunk transport; .simple/logs/cdb-smoke5.log)
- cycle-126: `mov rax,[rax]` rax=0 at simple_exe+0x24f83f (NULL dispatch
  pointer; .simple/logs/cdb-smoke7.log) — corruption moved downstream.

Workaround layer landed: PR #3611 (bind-once guards on the six remaining
double-read dict draws in module_lowering.spl, astra GO). The residual
defect is upstream's dict-value/ABI transport in the p2_add domain
(cycles 121-126 are actively chasing it: tuple-return ABI, erased dict
reads, feed-array poisoning). This doc + the three cdb captures are the
handoff evidence for their next cycles.

## Addendum 2026-10-17 (late): smoke9 — guards reach the box, the box is empty inside

Lane attempt 10 (with #3629 bind-once if-val guards on all three values()-drawn
loops) still AVs, now at RVA 0x58202d — same function lower_module_emit_fn_v1,
shifted by the guard code. Registers: r13=untag(fn-field)=0, r8=0x8000000000000000
(boxed header). The record PASSES if val (the draw is a Some box) but its PAYLOAD
word is nil-0: the owner-field array-element read emits a boxed optional with a
nil payload where a concrete HirFunction belongs. This is the compiler CODEGEN's
element-read transport (double-wrap), not a consumption-side nil — no source
guard can compensate. Producer fix belongs to upstream's p2_add cycles (their
escalation docs at cycles 144-154 are chasing the same class: "verbatim stores
in Tuple/Array/set_field arms; revert generic-path experiment", cycle-154).
Capture: .simple/logs/cdb-smoke9.log.
