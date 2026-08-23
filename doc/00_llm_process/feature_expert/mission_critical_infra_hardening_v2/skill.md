# Feature Expert: Mission-Critical Infrastructure Hardening V2

Use this expert for the selected compiler/SimpleOS/rendering/bounded-allocation
umbrella lane. Read the feature/NFR requirements, architecture, detail design,
system-test plan, and operator guide before editing.

Preserve these invariants:

- exact-current `PureSimple` compiler evidence only;
- selected SimpleOS subsets are scoped claims, never all-platform claims;
- every DrawIR-v3 plan is bound to one arena and generation;
- active rendering generations cannot grow or silently truncate;
- relaxed allocation is sealed, domain-local, quota-bounded, transactional,
  and forbidden in critical contexts;
- process kill/wait paths reject `pid <= 0` before owner-facade calls;
- missing, stale, skipped, synthetic, cached-only, or external-host-unavailable
  evidence blocks the applicable claim.

Do not promote the Rust bootstrap seed or Stage 2 into release evidence. The
old `runtime_compiler.spl` conflict is resolved. Current-head focused execution
is blocked by Stage 3 self-host exit 139 after fresh Stage 2 sanity; use
`doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md` and the canonical
ledger in `doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`.

## Wave 5 — warning-phase migration (planned 2026-08-23)

Plan: `doc/03_plan/agent_tasks/mission_critical_infra_hardening_v2.md` § "Wave 5".
Feature 1 (lane `mcwarn-1`): assurance warning phase — every diagnostic drops
exactly one severity rung, still reported (never silenced); a policy FIELD, not
a new profile name (alias table in `policy_names.spl` is FROZEN). Feature 2
(lane `mcalloc-1`): alloc-diagnostic knob — scoped/explicit opt-out only; a
global off-switch is rejected by design and `off` is invalid under
`critical`/`verified`. Migration M0-M5 moves driver/compiler, then loader, then
interpreter into critical-at-warning-level with a fail-closed gate per step.
The interpreter goes LAST: its projection of the profile table is a bool
(`match_fallthrough_profile_is_deny`) that cannot express a downgrade, so M3 is
a projection-widening change, not a config flip. Lane statuses above are
unverified by the planning lane.
