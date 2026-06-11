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
| `src/verification/aop_weaver/` | advice confluence, conflict-detection soundness, proceed exactly-once, no-match preservation | `compiler/10.frontend/core/aop.spl`, `85.mdsoc` matrix |
| `src/verification/gc_boundary/` (supersedes thin gc_manual_borrow/nogc_compile stubs — keep, extend) | no gc→nogc escape without copy; noalloc closure; inference monotonicity | `35.semantics/gc_boundary_check.spl`, `noalloc_checker.spl` |
| `src/verification/kernel_capabilities/` | non-escalation, attenuation, revocation, syscall-gate soundness | `os/kernel/ipc/capability.spl` |
| `src/verification/actor_channel/` | per-sender FIFO, actor isolation, no lost wakeup, bounded-send blocks | channel/green_channel/actor semantics incl. W2-7 closed-state |
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
