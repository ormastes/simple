# Layer Expert: Mission-Critical Memory

The selected relaxed-allocation profile, fault-injection evidence, and blocked
release rows are tracked by
`doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`.

Owner surfaces:

- `src/lib/nogc_sync_mut/mission_critical/domain_arena_v1.spl`
- `src/lib/common/mission_critical/draw_ir_generation_arena_v3.spl`
- `src/lib/nogc_sync_mut/mission_critical/bounded_process_policy.spl`

Rules:

- Strict absence/default means zero post-ready allocation in critical domains.
- Relaxation is arena-only: preallocated, sealed, hard quota, fixed alignment
  and allocation count, approved context mask, no global fallback.
- Allocation begins at a checkpoint. Publish only on commit; error rolls back
  cursor/count and advances generation so escaped references become stale.
- Exact capacity is valid; one unit/byte beyond rejects before mutation.
- Draw IR plans carry arena and generation identity. Active generations do not
  grow, clamp, truncate, or borrow capacity.
- Kernel, ISR, storage-commit, ownership-publication, and isolation-transition
  contexts always reject.
- New runtime imports are prohibited unless a recorded owner-boundary decision
  proves no existing facade can supply the capability.

## Alloc-diagnostic config knob (2026-08-23)

`src/compiler/00.common/mission_critical/alloc_diagnostic_config.spl` configures
the WP-12 steady-state allocation gate in `35.semantics/noalloc_checker.spl`.

- `McAllocDiagnosticConfig.default()` is EMPTY — the gate is fully live by
  default, and `check_steady_state_gate` is behaviourally unchanged.
- Opt-outs are per-symbol (or dot-bounded module prefix) and require a
  justification; `SIMPLE_MC_ALLOC_ALLOW="scope=why,..."` is parsed by
  `parse_alloc_allowances` (caller reads the env; the module stays state-free).
- Suppressed findings are still produced by `steady_state_findings` and printed
  as `allowed[steady-state]` — the check is disabled at a scope, never deleted.
- Guide: `doc/07_guide/language/mission_critical_alloc_diagnostic_config.md`.
