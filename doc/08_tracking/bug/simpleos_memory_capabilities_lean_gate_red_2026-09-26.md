# SimpleOS critical Lean gate: memory capabilities project remains red

Status: open after the third verify/fix cycle on 2026-09-26.

With Lean 4.30.0 and 4.33.0 installed, the real
`scripts/check/check-simpleos-critical-formal-proofs.shs` gate first stopped
in `memory_model_drf`. Its `hasDataRace` predicate omitted the cross-thread
condition used by the witness theorems. Adding that condition made
`lake build` for `memory_model_drf` pass (3 jobs).

The next full gate run passed `kernel_scheduler`, `actor_channel`,
`memory_model_drf`, and `kernel_capabilities`, then stopped at
`memory_capabilities`. The isolated logs are
`build/simpleos_formal_tools/critical_formal_after_fix.log` and
`build/simpleos_formal_tools/memory_capabilities.log`.

The remaining source errors are separate:

- `conversion_is_safe` leaves six Boolean equality cases unsolved under Lean
  4.33.0 (`MemoryCapabilities.lean:85`).
- Proofs of `singleton_env_wellformed`, `two_shared_env_wellformed`, and the
  negative exclusive/isolated examples expect a third invariant limiting the
  *combined* exclusive and isolated reference count. The current `wellFormed`
  definition declares only two individual limits.
- `shared_alias_create_read_only_policy` refers to an absent theorem
  `two_shared_read_only_at_location`.

One combined proof edit was tried. A targeted `lake build` still failed on
decidability and a shared-reference goal, so that edit was reverted. This
session reached the repository's three-cycle verify/fix cap for the critical
formal gate. Resume the repair in a fresh scoped session, prove the actual
capability invariant without weakening the theorem floor or trust scan, then
run the full gate once. No SimpleOS release qualification is claimed.
