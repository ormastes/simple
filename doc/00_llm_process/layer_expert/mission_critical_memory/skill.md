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

The arena context constants already exported for SCV must also have public
native declarations under recovered P2. This changes linkage visibility only;
quota and forbidden-context behavior still require runtime evidence. Keep
`DOMAIN_ARENA_U64_MAX` private. The 2026-10-29 SCV exported-static bug record
distinguishes native compilation success from unresolved behavior checks.
