# Phase3 post-HIR access violation and retained owner transport

Status: fix-implemented-verification-pending (2026-11-03). Exact fault
instruction is not established. Do not label this AV fixed from source review.

Evidence: windows-restart-20261004/p3-next916be-cranelift80/artifact/result.json
records compile_exit139/admittedfalse. build.rss.env reports abnormal Windows
status0xc0000005; worker tmp/native-build-stderr-9092-2.log (SHA256
94ce26870562293a504da85c791107e4d149318446ff43eb2d4b142d5fc86c82)
ends after1142/1142 HIR modules and cache summary. Profiling was unset, so the
absence of optional phase markers cannot identify which later operation faulted.
mem_snapshot_finish, summary field reads, context publication and subsequent
validation remain in the unresolved interval. No debugger attachment/dump used.

The retain-all implementation still copied the complete CompileContext for
summary reads and returned a context/verdict tuple for the caller to reinstall.
The streaming sibling already commits in place. The August20 SimpleOS incident
record documents earlier recovery after removing that ownership pattern; this
is supporting precedent, not proof of this Windows fault's exact cause.

Repair: retain-all lowering exposes a canonical me owner operation returning
only bool. Production orchestration consumes it directly and never converts a
malformed tuple plus zero errors into success. Summary reads use the owner.
The original tuple API remains a compatibility wrapper for existing callers;
general class/tuple code-generation correctness is not claimed repaired.

Regression coverage: existing dense physical alias lifecycle test now consumes
the scalar owner verdict and verifies committed HIR. A missing-surface case
checks false verdict, recorded error and retained sources. Existing route
contract test is updated to forbid synthetic recovery success. These tests and
all native correctness/RSS/time measurements are UNRUN. The ongoing streaming
successor is independent diagnostic evidence and must not be restarted.

Memory/performance review: removes a closure-sized local and production tuple
transport; adds no new retained aggregate or module scan. Later validation must
compare retained and streaming outputs/diagnostics and measure peak RSS/time on
the same frozen closure with a corrected producer. Existing log_phase boundaries
must be enabled in that bounded run before drawing a narrower fault conclusion.

**Revalidated 2026-11-02: still plausible because OPEN; ownership repair authored, native validation UNRUN. Exact fault; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 completion of the owner repair (lane-owner-av)

Finding: the 2026-10-05 repair (0f237fa8521) DID land the scalar owner
`lower_and_check_retained_owner_impl() -> bool`, and production routes through
it (`driver_stage_hir_v1.spl:48`, consumed by `driver_orchestration.spl:492`).
But two early exits inside that bool owner still returned the aggregate tuple:
`driver_hir_pipeline_lowering.spl:1600` `return (self.ctx, streamed_ok)` and
`:1603` `return (self.ctx, false)` (the E-DRV-PHASE3-EMPTY abort). A
`(CompileContext, bool)` value in a bool slot is exactly the malformed-tuple /
closure-sized-copy transport this repair meant to remove. Both now return the
scalar verdict.

Regression: `test/01_unit/compiler/driver/phase3_tuple_verdict_recovery_spec.spl`
gains "should never return an aggregate tuple from the boolean retained owner"
(FAILED before, passes after; spec 5/5 via `bin/simple.exe run`). Its route
assertions were also repointed at `driver_stage_hir_v1.spl`, where the routing
moved. `streaming_module_surface_lifecycle_spec.spl` cannot run on the current
seed (parse error "Unterminated f-string" in
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, pre-existing,
identical with and without this change); `entry_closure_physical_source_dedup_spec.spl`
is 8 pass / 6 fail identically with and without this change.

Native verification (still required; exact fault instruction unproven):
1. Build a stage3 Windows producer from a tree containing this change.
2. Run the Phase 3 native-build of the same frozen closure as
   `p3-next916be-cranelift80` (1142 modules) with log_phase/profiling enabled.
3. Pass = exit 0 past Phase 3 with no 0xc0000005; record peak RSS/time and
   compare retained vs streaming diagnostics. Keep any workaround tags until then.
