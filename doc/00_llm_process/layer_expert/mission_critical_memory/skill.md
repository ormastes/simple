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
