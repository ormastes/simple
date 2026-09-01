# Hardening + Formal Verification Plan (2026-06-11)

Goal: harden Simple in multithread / async / gc-nogc / AOP — prevent crashes,
stop crash propagation across tasks, make failures debuggable. Fix all known
bugs and pin each fix with a regression spec. Update and recheck the existing
Lean formal-verification backend; extend formal verification to complex
unverified parts (language, UI gui/tui, DB, SimpleOS).

Research basis:
`doc/01_research/runtime/crash_hardening/crash_surface_bug_lean_research_2026-06-11.md`.

Execution model: small parallel tasks, **disjoint file scopes**, Sonnet
implementers for easy/mechanical work, Fable orchestrator review + commit per
batch, Fable final review. Overhead policy: always-on fixes must be
zero-cost-on-happy-path; anything with per-call overhead goes behind a
`SIMPLE_*` env flag (presence = on), **default OFF**.

Standing constraints: fix root causes (no cover-ups), pure-Simple first (Rust
runtime edits only where panic-catching/poison-recovery is impossible from
`.spl`, with Simple-parity in the same commit), arch changes need user
go/no-go, regression specs verified in interpreter mode (no false-greens).

---

## Wave 1 — Known-bug fixes + regression specs

One Sonnet agent per row; each delivers root-cause fix + `*_spec.spl`
regression test (interpreter-mode green) + bug doc status update.

| ID | Bug doc | Scope (disjoint) | Difficulty |
|----|---------|------------------|-----------|
| B1 | `array_push_loop_in_main_len_coredump_2026-06-11` | interpreter/codegen array push+len path | hard — Fable/Opus assist |
| B2 | `async_await_interpreter_crashes_2026-06-11` | interpreter async/await eval | hard |
| B3 | `memory_capabilities_interpreter_crashes_2026-06-11` | interpreter enum-field method dispatch | medium |
| B4 | `codegen_stub_fallback_silent_exit0_2026-06-11` | native codegen stub fallback → hard error (flag `SIMPLE_ALLOW_STUB_FALLBACK` to restore old behavior) | medium |
| B5 | `rt_file_exists_bool_vs_int_interpreted_resolver_2026-06-10` | interpreted resolver | easy |
| B6 | `green_thread_direct_runtime_blockers_2026-06-06` (eager green_spawn) | `concurrent/green_thread.spl` + scheduler glue | medium |
| B7 | `argv_main_spl_suffix_misroute` latent copies (~14 sites) | grep-driven sweep, mechanical | easy |
| B8 | `expect_call_expr_hollow_false_green_2026-06-10` | spec runner matcher path | medium (test-integrity priority) |
| B9 | Recheck `release_binary_compile_broken` + `selfhosted_mcp_binary_segfault` against 2026-06-11 stage4 fixes; close or re-scope | verification only | easy |
| B10 | Status triage: sweep the ~111 no-status bug docs; mark fixed-by-now vs open (sample-verify) | doc/08_tracking/bug only | easy |

Rule: every fix lands with its spec in the same commit. Specs that cannot go
green in the current build state are NOT shipped half-done (no skip()/weakened
asserts) — the bug stays open with a note.

## Wave 2 — Crash hardening (H1–H11)

Grouped by disjoint scope. Always-on items are zero-overhead-on-success;
diagnostic items are flag-gated, default off.

| Task | Holes | Files | Always-on or flagged |
|------|-------|-------|---------------------|
| W2-1 Executor panic boundary | H2 | `runtime/src/executor.rs` | always-on: `catch_unwind` around `task.execute()`, wire to `Promise.reject("task {id} panicked: {msg}")`; worker survives |
| W2-2 Actor death reason + real join | H4, H5 | `runtime/src/value/actors.rs`, `runtime/src/concurrency/mod.rs` | always-on: join slot holds real handle; `rt_actor_join` failure exposes reason string extern (`rt_actor_death_reason`) |
| W2-3 Poison-proof registries | H9 | `runtime/src/value/sffi/concurrent/{map,queue,pool,stack,tls}.rs`, executor task-queue lock | always-on: `unwrap_or_else(|e| e.into_inner())`; optional `SIMPLE_LOCK_TRACE` log on recovery |
| W2-4 AOP error visibility | H10, H11 | `runtime/src/aop.rs`, `src/lib/*/src/aop.spl` | always-on: panic → recorded error (last-aop-error extern + stderr line), not silent NIL; advice-Err logged when join point skipped. `SIMPLE_AOP_TRACE` for verbose |
| W2-5 Task error surfacing (.spl) | H1, H3 | `async_host/scheduler.spl`, `async_host/runtime.spl`, `handle.spl` | always-on: populate `HostTaskHandle.error`; scheduler records death reason + task key, removes task, keeps worker alive |
| W2-6 Actor scheduler dispatch errors (.spl) | H6 | `actor/scheduler.spl` | always-on: inspect `DispatchResult`, count + retain last error per actor; `SIMPLE_ACTOR_TRACE` for per-message log |
| W2-7 Channel closed-state signaling | H7, H8 | `nogc_sync_mut/concurrent/channel.spl`, `nogc_async_mut/concurrent/green_channel.spl` | additive API: `try_send -> Result`, `close()`+closed flag for GreenChannel, parked-receiver wake-on-close; existing `send` behavior unchanged (compat) |
| W2-8 Debug toggles + docs | — | task_identity glue, `doc/07_guide/` | flagged: `SIMPLE_TASK_TRACE`, `SIMPLE_ACTOR_BACKTRACE` (capture backtrace on death), all default off |

Rust edits here are justified (panic catching/lock poisoning unreachable from
`.spl`); each W2 Rust task updates the pure-Simple wrapper/callers in the same
commit (Rust/Simple parity rule). Each W2 task ships a regression spec
(panic-in-task survives + reports; poisoned-lock recovery; AOP panic visible;
closed-channel signaling).

## Wave 3 — Lean formal verification

### 3a — Recheck/update existing (mechanical, Sonnet)
| Task | Scope |
|------|-------|
| L1 | Add lakefiles + pinned `lean-toolchain` (single repo-wide pin) to the 10 projects lacking them; `lake build` each; fix tactic drift |
| L2 | nvfs: bump pin v4.14.0-rc2 → repo pin; `lake build`; fix tactic breakage |
| L3 | std proofs project: replace floating `stable` with repo pin; build |
| L4 | `simple gen-lean compare` for `AsyncEffectInference.lean`; if regenerator drifted from runtime async semantics, regenerate + reprove |
| L5 | Re-read visibility/module_resolution/macro proofs against the field-wrapper accessor changes; update models if semantics moved |
| L6 | CI gate: `scripts/check/check-lean-proofs.shs` building all projects, failing on `sorry`/errors (wired into `bin/simple build check` as opt-in lane) |

### 3b — New P1 models (match CURRENT architecture; verification only)
| Model | Proves | Source of truth |
|-------|--------|----------------|
| `src/verification/aop_weaver/` ✓ DONE 2026-06-11 | T1 selection_sorted, T2 selection_stable, T3 no_match_preserves, T4 deny_skips_target, T5 deny_monotone (handler-mono hyp), T6 proceed_linear — `lake build` zero sorry; F1 Around pre-hook/proceed-chain split, F2 stability tiebreaker divergence, F3 After-denial masks result | `src/lib/nogc_sync_mut/src/aop.spl`, `src/compiler_rust/runtime/src/aop.rs` |
| `src/verification/gc_boundary/` (supersedes thin gc_manual_borrow/nogc_compile stubs — keep, extend) | no gc→nogc escape without copy; noalloc closure; inference monotonicity | `35.semantics/gc_boundary_check.spl`, `noalloc_checker.spl` |
| `src/verification/kernel_capabilities/` | non-escalation, attenuation, revocation, syscall-gate soundness | `os/kernel/ipc/capability.spl` |
| `src/verification/actor_channel/` ✓ DONE 2026-06-11 | T1 fifo_per_sender, T2a closed_send_reports_failure, T2b closed_empty_recv_no_park, T2c legacy_try_send_closed_fails, T3 close_drains_parked + close_wakes_all_parked, T4a process_one_at_most_one, T4b process_one_preserves_fifo, T5 dispatch_error_no_halt + scheduler_error_no_halt, T6a no_lost_task_send, T6b no_lost_task_close, T6c no_lost_task_recv_parks, T-fact legacy_send_closed_noop + legacy_try_send_closed_no_enqueue — `lake build` zero sorry | channel/green_channel/actor semantics incl. W2-7 closed-state |
| `src/verification/db_storage/` | B-tree ordered+balanced under split/merge; WAL-before-data; snapshot isolation; recovery equation | `os/services/nvfs/core/pmap_btree.spl`, dbfs_engine |

### 3c — P2/P3 queue (after 3b lands)
Kernel scheduler (starvation-freedom, queue integrity), FAT32 (single-owner
chains, crash safety), UI compositor (diff-render = full-render, layout
termination, session state machine). UI/TUI/DB/SimpleOS complex parts thereby
all get coverage; P2/P3 starts only after P1 review.

If any proof attempt reveals the IMPLEMENTATION violates a stated invariant:
that is a bug → goes to Wave-1-style fix + regression spec. If the invariant
itself is wrong/needs an arch change: escalate for user go/no-go, do not
auto-change architecture.

## Parallelization map

| Team | Model | Tasks | Files (disjoint) |
|------|-------|-------|------------------|
| S1 | Sonnet | B5, B7, B10 | resolver, argv sweep, bug-doc statuses |
| S2 | Sonnet | B3, B8 | interpreter dispatch, spec runner |
| S3 | Sonnet | W2-3, W2-1 | sffi/concurrent/*, executor.rs |
| S4 | Sonnet | W2-5, W2-6 | async_host/*.spl, actor/scheduler.spl |
| S5 | Sonnet | W2-7 | channel.spl, green_channel.spl |
| S6 | Sonnet | L1–L3, L6 | src/verification lakefiles, scripts/check |
| F1 | Fable (orchestrator) | B1, B2, B4, B6, W2-2, W2-4, L4, L5 review+hard parts | — |
| F2 | Fable | review every diff, commit per batch, final review, docs/guide/spipe update | — |

Lean 3b models: one Sonnet agent per model drafting state machine + invariants,
Fable proves/reviews the theorems (proof debugging is not "easy task").

Commit discipline: per-batch commits immediately after review (parallel-jj
clobber risk); push via jj, fall back to git-plumbing+SSH on reconcile races.

## Definition of done
1. All explicitly-open bugs fixed-or-rescoped with regression specs; no-status
   docs triaged.
2. H1–H11 closed; panic in any task/actor/advice no longer kills siblings or
   the process, and leaves a queryable death reason; all diagnostics flag-gated
   per overhead policy.
3. All Lean projects build under one pinned toolchain with zero sorry; stale
   models updated; 5 new P1 models landed; check script wired.
4. Docs/guides/spipe skill updated; everything pushed to origin/main.

---

## FINAL STATUS — 2026-06-11 (Fable review)

DoD 1: DONE (B1 verified-fixed+pinned, B2 partially-fixed [await corruption
fixed; generator/actor desugar reconcile tracked in bug doc], B3/B4/B5/B7/B8
fixed+pinned, B6 blockers were already fixed [cooperative-deferral design
remains, see escalations], B9a resolved-by-redeploy / B9b blocked-on-deploy,
B10 all 201 bug docs carry Status). DoD 2: DONE (executor/actor/AOP/channel/
scheduler hardening landed; toggles SIMPLE_ACTOR_TRACE etc. default-off; seed
rebuilt + redeployed + smoke-tested). DoD 3: DONE (18/18 Lake projects PASS
under auto-discovering `scripts/check/check-lean-proofs.shs`, zero sorry; all
5 P1 models landed: aop_weaver, gc_boundary, kernel_capabilities,
actor_channel, db_storage; L4/L5 staleness audit = all CURRENT). DoD 4: DONE
(crash_debugging guide, verify-skill checklist, plan/research docs; ~12
batches pushed to origin/main via sync cycle).

### Escalations — need user go/no-go (NOT implemented)
1. **AOP F1 — runtime Around is a pre-hook** (was Item 2 / Option A in
   security_followups_phase2): `.spl` weaver never reaches the proceed-chain
   in `aop.rs`; unify or document-and-restrict. Design revised per earlier
   Fable review; awaiting decision.
2. **AOP F3 — After-advice denial masks the join-point result** (target ran,
   result lost). Needs a `Result`-shape decision.
3. **Kernel caps F1 — `revoke()` is non-transitive**: copies held by other
   principals survive revocation. Transitive revoke = semantic change.
4. **Kernel caps F2 — no delegation-depth field** in `CapabilityToken`;
   attenuation depth bound unenforced (model assumes it).
5. **db FINDING-T4 — pager.write_page has no page_lsn / WAL check**;
   WAL-before-data holds only at the txn.spl protocol level.
6. **B6 — cooperative green_spawn deferral**: green_spawn still evaluates
   eagerly; true deferral needs scheduler integration (design work).
7. **PhaseResult headers (ESCALATE 10, carried over)** — async http_server
   `Respond` still cannot carry response headers.

### Tracked follow-ups (no approval needed)
- gen-lean layer-3 drift (`LeanFunction.add_param`) + pre-existing lean_*
  spec failures + stale summary.txt — bug doc
  `gen_lean_regeneration_pipeline_broken_2026-06-11.md`.
- B4 note: next bootstrap-from-scratch run will surface any functions that
  previously relied on silent stub fallback as hard errors
  (`SIMPLE_ALLOW_STUB_FALLBACK` is the temporary escape hatch).
- csrf_spec phantom rewrite (carried over from phase 2).

---

## Wave 3b — gc_boundary Lean model (DELIVERED 2026-06-11)

**Location:** `src/verification/gc_boundary/`
**lake build:** zero errors, zero sorry, zero warnings (6 jobs green)
**Toolchain:** `leanprover/lean4:v4.30.0`

### Files

| File | Purpose |
|------|---------|
| `GcBoundary/Basic.lean` | Tiers, AllocAnn lattice, Expr language, HasTier, CheckerOk, noallocBodyOk |
| `GcBoundary/Theorems.lean` | AliasFree predicate + T1–T4 proved without sorry |
| `GcBoundary/AliasCounterexample.lean` | Alias-blindness counterexample (documented, not a sorry) |

### Theorems (zero sorry)

| ID | Name | Meaning |
|----|------|---------|
| T1 | `check_sound_wrt_model` | Checker acceptance in nogc/noalloc ⟹ no gc tier (alias-free fragment; `AliasFree env e` explicit in hypotheses) |
| T2 | `noalloc_closed` | `noallocBodyOk` (recursive walk) ⟹ `¬ EvalAllocates` |
| T3 | `inference_monotone` | `a ≤ b → a ≤ join b c`; fixpoint never removes `alloc` |
| T4 | `copy_isolates` | `HasTier fc env (Copy e) Tier.nogc` for any source; corollary: copy result ≠ gc |

### Alias-blindness counterexample

`counterEnv = [(0, gc)]`, `aliasExpr = Var 0`: has gc tier (proved), not AliasFree
(proved), real checker accepts it (no import-edge violation). T1 does not apply.
Precisely models the HIGH audit finding in `gc_nogc_memory_audit_findings_2026-06-11.md`.

### Implementation notes

- `HasTier.lit`/`HasTier.call` carry explicit equality hyps to avoid struct-field
  dep-elim restriction in Lean 4 index unification.
- `noallocBodyOk` is recursive (matches real checker's full-body walk); T2 uses
  `private def` structural recursion because `Expr` is a nested inductive.

---

## Wave 3b — actor_channel Lean model (DELIVERED 2026-06-11)

**Location:** `src/verification/actor_channel/`
**lake build:** zero errors, zero sorry, zero warnings (5 jobs green)
**Toolchain:** `leanprover/lean4:v4.30.0`

### Files

| File | Purpose |
|------|---------|
| `ActorChannel/Basic.lean` | LTS model: GreenChannel, SyncChannel, ActorState, SchedulerState; all step functions (greenSend, greenRecv, greenCloseDrain, legacySend, legacyTrySend, processOne, runOnce) |
| `ActorChannel/Theorems.lean` | 13 theorems (T1–T6 + T-fact) proved without sorry |
| `ActorChannel.lean` | Root import |
| `lakefile.toml` | Lake build config |
| `lean-toolchain` | Pinned `leanprover/lean4:v4.30.0` |

### Theorems (zero sorry)

| ID | Name | Meaning |
|----|------|---------|
| T1 | `fifo_per_sender` | Two sends into a fresh cap≥2 channel are received in send order |
| T2a | `closed_send_reports_failure` | `greenSend` to a closed channel returns `channel_closed=true, sent=false` (not silent drop) |
| T2b | `closed_empty_recv_no_park` | `greenRecv` on closed+empty channel returns immediately with `parked=false` |
| T2c | `legacy_try_send_closed_fails` | `legacyTrySend` returns `false` on closed channel (no enqueue) |
| T3a | `close_drains_parked` | After `greenCloseDrain`, `waiting_task_ids = []` |
| T3b | `close_wakes_all_parked` | Every tid that was in `waiting_task_ids` appears in `woken_task_ids` |
| T4a | `process_one_at_most_one` | `processOne` mailbox length is non-increasing (at most one dispatch) |
| T4b | `process_one_preserves_fifo` | After `processOne`, mailbox = original tail (FIFO order preserved) |
| T5a | `dispatch_error_no_halt` | Handler error increments `error_count`, sets `last_error`, actor stays alive |
| T5b | `scheduler_error_no_halt` | `runOnce` on error increments `total_errors`, returns `more=true`, actor stays alive |
| T6a | `no_lost_task_send` | A parked task is either still waiting or was unparked as `receiver_task_id` by send |
| T6b | `no_lost_task_close` | A parked task appears in `woken_task_ids` after `greenCloseDrain` |
| T6c | `no_lost_task_recv_parks` | A task that calls recv on open+empty appears in `waiting_task_ids` |
| T-fact a | `legacy_send_closed_noop` | `legacySend` to closed channel enqueues anyway (no closed check — impl fact, not violation) |
| T-fact b | `legacy_try_send_closed_no_enqueue` | `legacyTrySend` to closed channel does NOT enqueue |

### Implementation notes

- `GreenChannel` is a pure-functional LTS — all step functions are total and return result structs, exactly mirroring `green_channel.spl`.
- `private theorem hd_cons`: Lean 4.30.0 has no `List.head!_cons` lemma; proved `(a :: t).head! = a` by `rfl` and used as a local simp lemma throughout.
- `Type*` is not valid in Lean 4.30.0 universe-polymorphic position for `private theorem`; use `Type _` instead.
- T1 proof: `simp only` cannot reduce Bool `if false then` branches without the full simp set; `simp [greenSend, greenRecv, h1, h2, hd_cons]` closes the goal.
- T5/scheduler: `unfold runOnce processOne` leaves a nested `match rOpt` unreduced; `simp [hnotok, halive]` collapses it.
- `deriving instance Inhabited for ActorMessage` required at top of Theorems.lean for `List.head!` on `List ActorMessage`.

---

## Wave 3b — DB Storage Engine Invariants (2026-06-11)

**Location:** `src/verification/db_storage/`
**Lean version:** `leanprover/lean4:v4.30.0` (pinned, matches gc_boundary template)
**Status:** `lake build` green, zero errors, zero sorry.

### Source of truth

| File | Layer |
|------|-------|
| `src/os/services/nvfs/core/pmap_btree.spl` | B-tree (pmap_btree) |
| `src/lib/nogc_sync_mut/storage/shared/wal.spl` | WAL / SharedWal |
| `src/lib/nogc_sync_mut/db/dbfs_engine/mvcc.spl` | MVCC visibility |
| `src/lib/nogc_sync_mut/db/dbfs_engine/txn.spl` | D4 write protocol |
| `src/lib/nogc_sync_mut/db/dbfs_engine/pager.spl` | Pager (FINDING-T4) |

### Theorems proved (T1–T6)

| ID | Lean name | Statement |
|----|-----------|-----------|
| T1 | `T1_btree_ordered` | `orderedInsert` on a fresh key preserves strict key ordering |
| T2a | `T2_btree_balanced_leaf` | Leaf split produces two nodes both at height 0 |
| T2b | `T2_btree_balanced_internal_split` | Children from take/drop of a uniform-height list remain uniform-height |
| T3a | `T3_btree_bounds_split` | After split of a full node, both halves satisfy `[minKeys, maxKeys]` |
| T3b | `T3_btree_bounds_insert_nonfull` | Insert into a non-full node keeps length `≤ maxKeys` |
| T4a | `T4_wal_before_data` | `txnCommit` returns `some` only when `wal_flushed = true` |
| T4b | `T4_wal_appended_before_commit` | Full D4 chain (append→flush→commit) implies `wal_appended = true` on result |
| T5a | `T5_snapshot_committed` | A visible version was committed before snapshot (`commit_ts < xmax`) |
| T5b | `T5_snapshot_excludes_future` | A version committed after the snapshot is not visible |
| T5c | `T5_snapshot_excludes_deleted` | A version deleted by a committed txn before the snapshot is not visible |
| T6a | `T6_recovery_equation` | Every entry in the replay set has `lsn ≥ checkpoint`, type=data, committed txn |
| T6b | `T6_recovery_complete` | Every committed DATA record since checkpoint appears in the replay set |

### Source fidelity notes

- `minKeys(t) = t / 2` (integer division) — faithful to `fanout / 2` in `pmap_btree.spl`, not CLRS `t-1`.
- `maxKeys(t) = 2*t - 1` — faithful to impl.
- Leaf split: left keeps `keys[0..t-2]`, right keeps `keys[t..]`, median promoted to parent only.
- T1 requires `hfresh : ∀ x ∈ ks, k ≠ x` — inserting a duplicate into a strictly-ordered list is impossible (would require `k < k`); this models the B-tree invariant that keys are unique.
- WAL LSN starts at 1, `walAppend` assigns `next_lsn` then increments — mirrors `SharedWal.append`.
- MVCC `snapshotSees` mirrors the 6 visibility rules in `mvcc_is_visible` (R1–R6).

### FINDING-T4 — pager WAL-before-data gap

`pager.write_page` in `pager.spl` marks a `PageEntry` dirty but carries **no `page_lsn` field** and does **not** consult `wal.durable_lsn`. WAL-before-data is enforced only at the D4 protocol level (step ordering in `txn.spl`), not at the pager layer. T4 models only the protocol-level enforcement. A pager-layer LSN check would be a separate hardening item.

Reference: `src/lib/nogc_sync_mut/db/dbfs_engine/pager.spl` — `write_page`, `flush_dirty`.

### Implementation notes (Lean 4.30.0)

- `meta` is a reserved keyword in Lean 4.30 — renamed to `metaRec` in `RecordType`.
- `List.not_mem_nil` in 4.30 has type `False` (not `¬ a ∈ []`); use `exact nomatch h` for membership-in-empty goals.
- `List.Mem.head` and `List.Mem.tail` are the correct constructors (not `List.mem_cons_self`).
- `LawfulBEq RecordType` must be stated manually; `deriving LawfulBEq` fails because `deriving BEq` from `DecidableEq` does not auto-register the lawful instance. Proved via `cases a <;> cases b <;> first | rfl | exact absurd h (by decide)`.
- `Bool.false_ne_true` used for Bool contradiction in T5c (`hactive ▸ Bool.false_ne_true`).
- T6 filter membership: `simp only [Bool.and_eq_true, decide_eq_true_eq]` normalises the filter predicate into a conjunction of Props; `beq_iff_eq` is NOT needed separately once `LawfulBEq` is available (simp applies it automatically).
