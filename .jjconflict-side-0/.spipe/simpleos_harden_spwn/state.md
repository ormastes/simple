# Lane SPWN — P8×P2 meet-point: profile attenuation ∧ spawn rights at spawn time

## Goal
Land the recorded cross-lane hand-off from
`.spipe/simpleos_production_host_master_plan/state.md`: "P8 resolve_effective +
P2 spawn_spec_effective_rights must meet at spawn time" — one pure meet-point
function composing both attenuations with deny-wins semantics, wired at the
spawn decision point, spec'd, no boot-seal arming.

## Decisions
- Meet point = `spawn_effective_rights_with_profile(parent_rights, requested_rights, profile_mask) -> u32`
  in `src/os/kernel/loader/spawn_authority.spl` — pure triple intersection
  (`parent & requested & profile_mask`), no IO, provable. Kept the rights type
  `u32` (the CAP_RIGHT_* space used by every other fn in the module) rather than
  the task's suggestive `i64`.
- `SPAWN_PROFILE_MASK_ALL: u32 = 0xFFFFFFFFu32` is the meet identity: callers
  without a profile pass it and are bit-for-bit unchanged (non-LLM spawns
  unaffected; spec-proven).
- Decision-point wiring = `spawn_spec_effective_rights_with_profile(spec,
  parent, exec_ceiling, system_ceiling, denials, profile_mask)`: §5.4 SpawnSpec
  formula first, then the meet. Base result is already ⊆ parent, so the meet
  only ever removes bits.
- Adapter side: `profile_spawn_adapter.llm_spawn_effective_rights` now routes
  through the single meet function (same value as its former inline triple
  intersection — adapter spec proves no regression). Unmapped/unknown LLM
  rights still resolve to 0 in `llm_profile_to_spawn_rights` BEFORE the mask is
  built (fail closed).
- Boot seal NOT armed: `spawn_authority_seal_bootstrap` call sites unchanged;
  no syscall_process.spl / boot-file edits (out of lane ownership + needs QEMU
  evidence).

## Evidence (build/spwn_job = bin/release/x86_64-unknown-linux-gnu/simple, `run` verb)
- `test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl`:
  5 + 6 + 5 examples, 0 failures (16 total; was 11 — +5 meet-point cases:
  result ⊆ each of three inputs with absolute values, ALL-mask identity vs
  `spawn_spec_effective_rights`, profile cannot add a parent-lacked right,
  all-deny profile ⇒ 0, partial profile mask at the SpawnSpec decision point).
- `test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl`:
  2 + 1 + 3 + 3 examples, 0 failures (9 total, unchanged).
- `test/01_unit/os/security/llm_profile_attenuation_spec.spl`:
  4 + 3 + 2 + 5 + 4 examples, 0 failures (18 total, unchanged).

## Files
- `src/os/kernel/loader/spawn_authority.spl` — meet-point section (+~60 lines)
- `src/os/security/llm_profiles/profile_spawn_adapter.spl` — routed through meet
- `test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl` — +5 examples
- `doc/08_tracking/os/production_status.sdn` — capability_spawn + llm_profiles note lines

## Next (blocked rows)
- **Live spawn-syscall wiring** (blocked: `syscall_process.spl` owned by
  another lane / ABI freeze). Resume: wire
  `spawn_spec_effective_rights_with_profile` at the 3 ambient-guard syscall
  sites + fs_exec bridge, passing `llm_profile_to_spawn_rights(profile)` when
  the caller carries a profile, `SPAWN_PROFILE_MASK_ALL` otherwise. Verify:
  `build/spwn_job run test/01_unit/os/kernel/loader/spawn_authority_contract_spec.spl`.
- **Boot seal arming** (blocked: needs QEMU boot evidence that init still comes
  up sealed). Resume: flip `_seal_ambient_spawn_on_boot` path, then
  real-firmware QEMU boot per `.claude/rules/board-runnable.md` (OVMF pflash),
  capture serial transcript showing `[spawn-auth] bootstrap sealed`.
