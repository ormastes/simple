# Crash Hardening + Formal Verification — Research Synthesis (2026-06-11)

Inputs from 4 parallel research agents (bug inventory, concurrency crash surface,
Lean verification audit, unverified-complex map). Drives the plan at
`doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md`.

## 1. Known-bug inventory (summary)

- `doc/08_tracking/bug/`: **161 bug docs**; 15 explicitly OPEN, ~35 resolved,
  ~111 with no status line (treat as open-by-context until rechecked).
- **26 crash/hang/leak bugs**; only **4 bugs have any regression spec**
  (hir_any_field, sha384_kat, u8_push_literal, match_empty_array). The
  prevention gap is the dominant finding: fixed bugs routinely re-regress
  because nothing pins them.
- Top open crashers in goal areas (multithread/async/gc-nogc/AOP/runtime):
  - `array_push_loop_in_main_len_coredump_2026-06-11` — SIGSEGV native AND interpreter.
  - `async_await_interpreter_crashes_2026-06-11`.
  - `memory_capabilities_interpreter_crashes_2026-06-11` — enum-field method call crash.
  - `codegen_stub_fallback_silent_exit0_2026-06-11` — silent wrong binaries.
  - `std_async_runtime_native_backend_gaps_2026-06-11`.
  - `green_thread_direct_runtime_blockers_2026-06-06` — green_spawn is EAGER
    (runs closure at spawn time; no cooperative deferral, no error boundary).
  - `release_binary_compile_broken_2026-06-02`, `selfhosted_mcp_binary_segfault_2026-06-02`
    — recheck against the 2026-06-11 stage4 chain fixes before re-fixing.
  - `gc_nogc_memory_audit_findings_2026-06-11` — "gc" mode is allocate-and-leak;
    boundary check is lint-only and alias-blind.

## 2. Concurrency/async/AOP crash holes (H1–H11)

| # | Hole | Where | Class |
|---|------|-------|-------|
| H1 | Task panic kills scheduler OS thread; queued tasks abandoned, no death reason | `src/lib/nogc_async_mut/async_host/scheduler.spl:228` (`t.poll_fn()` bare) | propagation |
| H2 | Executor worker panic swallowed (`task.execute()` no catch; `_ = handle.join()`) | `src/compiler_rust/runtime/src/executor.rs` | propagation+silent |
| H3 | `HostTaskHandle.error` never populated — failures unobservable by joiners | `src/lib/nogc_async_mut/async_host/runtime.spl` | silent |
| H4 | `rt_actor_join` returns 0 on actor panic; reason lost | `src/compiler_rust/runtime/src/value/actors.rs:163` | silent |
| H5 | Scheduler join slot registered empty; `join_actor(id)` always no-ops | `src/compiler_rust/runtime/src/concurrency/mod.rs:61` | silent |
| H6 | `ActorScheduler.run_until_idle` drops `DispatchResult` handler errors | `src/lib/nogc_async_mut/actor/scheduler.spl` | silent |
| H7 | `Channel.send` to closed channel = silent no-op | `src/lib/nogc_sync_mut/concurrent/channel.spl` | silent |
| H8 | `GreenChannel` has no closed/dead state; parked receivers leak forever | `src/lib/nogc_async_mut/concurrent/green_channel.spl` | leak/hang |
| H9 | `.lock().unwrap()` on global registry mutexes — one panic poisons whole process (814 unwraps in runtime/src; 58 in sffi/concurrent) | `src/compiler_rust/runtime/src/value/sffi/concurrent/*` + `executor.rs` task queue | propagation |
| H10 | AOP Before/Around advice `Err` silently skips join point when caller ignores Result | `src/lib/nogc_sync_mut/src/aop.spl` `wrap()` | silent |
| H11 | `rt_aop_invoke_around` converts advice/proceed panic to NIL, no log (incl. "proceed not called exactly once" panic) | `src/compiler_rust/runtime/src/aop.rs:111` | silent |

Reusable mitigation patterns already in-tree:
- `catch_unwind(AssertUnwindSafe(..))` pattern exists in `aop.rs`.
- `SIMPLE_<NAME>` env-toggle convention: `std::env::var_os("SIMPLE_TORCH_TRACE").is_some()`
  — presence enables; absence = zero-cost default-off. Use for all new
  overhead-adding diagnostics.
- `current_unified_task_key(fallback)` (`async_host/task_identity.spl`) — ready
  to stamp task IDs into error/death messages.
- `Promise.reject(error)` (`executor.rs`) — working error path; wire panics to it.
- Poison recovery: `.lock().unwrap_or_else(|e| e.into_inner())` — zero overhead
  on the happy path.

## 3. Lean verification — existing state

- 12 projects under `src/verification/` + 5 proofs in
  `src/compiler_rust/lib/std/src/**/proofs/` + `src/app/gen_lean` (CLI wrapper
  over `simple gen-lean generate|write|compare|verify`) +
  `test/00_formal_verification/` (emitter/codegen specs, all green; they do NOT
  invoke lean).
- All proof files: **zero real `sorry`** (the one grep hit in nvfs is a doc comment).
- **Most projects have NO lakefile** — they have never been machine-checked as
  Lake projects. Only `formal/nvfs` (lakefile.toml, pinned `lean4:v4.14.0-rc2`)
  and the std proofs project (`lakefile.lean`, floating `lean4:stable`) build.
- Toolchain installed: lean 4.30.0, lake 5.0.0, elan 4.1.2. nvfs pin is 16
  minor releases behind stable; std floats (silent breakage risk).
- Staleness ranking: (1) `AsyncEffectInference.lean` is AUTO-GENERATED from
  `regenerate/async_effect_inference.spl` — regenerator may lag the runtime
  async protocol; (2) visibility/module_resolution proofs vs recent
  field-wrapper/accessor changes; (3) macro auto-import; (4) nvfs tactic drift
  across Lean versions.
- Biggest semantic gap: actor/green scheduler, cooperative suspension, channel
  semantics, and reservation analysis are **entirely unmodeled**;
  `AsyncCompile.lean` only models a 3-effect enum.

## 4. New formal-verification candidates (complex, unverified)

| Pri | Subsystem | Bulk files | Key invariants | Tractability |
|-----|-----------|-----------|----------------|--------------|
| P1 | AOP weaver semantics | `compiler/10.frontend/core/aop.spl` (547), `50.mir/mir_aop_injection.spl`, `85.mdsoc/weaving/*`, `runtime/src/aop.rs` | advice confluence; conflict-detection soundness; `proceed` exactly-once; no-match ⇒ behavior preserved; gc/nogc annotations preserved through weaving | Medium |
| P1 | GC/nogc boundary | `compiler/00.common/gc_boundary.spl`, `35.semantics/gc_boundary_check.spl`, `noalloc_checker.spl`, `runtime/src/memory/*`, `concurrent/gc_barrier.rs` | no gc pointer escapes into nogc without copy; noalloc never reaches alloc site; inference monotone; barrier never runs in nogc region | High (replaces 29/49-line stubs) |
| P1 | Kernel capabilities (OS IPC) | `os/kernel/ipc/capability.spl` (707), `capability_types.spl`, syscall gate | non-escalation; attenuation; revocation completeness; syscall-gate soundness | High (seL4/CHERI-style lattice) |
| P1 | simple_db storage (pmap_btree/WAL/MVCC) | `os/services/nvfs/core/pmap_btree.spl` (920), dbfs_engine wal/mvcc/txn | B-tree ordered+balanced across split/merge; WAL-before-data LSN ordering; snapshot isolation; recovery = checkpoint + replay | High (canonical) |
| P1 | Actor/channel/green-thread semantics | actor.spl, green_thread.spl, green_channel.spl, channels.rs, kernel green_carrier | FIFO per sender; actor isolation between dispatches; no lost wakeup/task; starvation-freedom; bounded send blocks not drops | Medium (LTS/CSP style) |
| P2 | SimpleOS kernel scheduler | `os/kernel/scheduler/*` (~3.9k lines) | no starvation; queue integrity; one-class-at-a-time; context-switch atomicity | Medium |
| P2 | FAT32 | `os/services/fat32/*` (~2.7k) | single-owner cluster chains; dir/FAT size agreement; crash safety | Medium (FSCQ-style) |
| P3 | UI compositor/session | `os/compositor/wm_scene.spl` (1769) etc. | diff-render = full-render; layout termination; z-order consistency; session state machine | Medium |

## 5. Conclusions feeding the plan

1. Regression-spec coverage (4/161) is the cheapest highest-leverage fix:
   every bug fixed in this effort ships with a pinned spec.
2. Crash propagation has a small set of root patterns (bare poll/execute,
   swallow-on-join, poisoned-lock cascade, error-to-NIL) — fixable with the
   in-tree `catch_unwind` + poison-recovery + `Promise.reject` patterns plus
   death-reason recording keyed by `current_unified_task_key`.
3. Always-on fixes must be zero-overhead-on-happy-path; anything that adds
   per-call cost (backtraces, tracing, verbose channel diagnostics) goes behind
   `SIMPLE_*` env flags, default OFF, per the established convention.
4. Lean work splits into mechanical CI hardening (lakefiles, pinned toolchain,
   build-all gate, gen-lean compare) and new P1 models that match the CURRENT
   architecture (no arch change required to verify; verification findings that
   demand arch changes get escalated, not auto-implemented).
