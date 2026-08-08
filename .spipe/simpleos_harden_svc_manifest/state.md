# Lane SVC — Typed Service Manifest Contract (service_v1)

**Program:** SimpleOS production harden — Phase 4
**Master plan:** doc/01_research/domain/simpleos_production_host_master_plan.md §4 (service_v1), §20 (health/watchdog/restart), §21 (restart-no-stale-grant invariant)
**Status:** MODEL + SPEC COMPLETE (working copy, not committed)

## Deliverables
- `src/os/services/service_manifest.spl` — typed `ServiceManifest` + pure lifecycle state machine.
- `test/01_unit/os/services/service_manifest_spec.spl` — 11 absolute-oracle examples.

## Manifest fields (`ServiceManifest`)
| Field | Type | Meaning |
|-------|------|---------|
| name / version | text | service identity |
| required_capabilities | [text] | grant ids/labels the service needs |
| readiness_deps | [text] | service names that must be Ready first |
| health_check_kind | text | none / ping / heartbeat |
| restart_policy | text | never / on_failure / always |
| max_restarts | i64 | cap within the restart window |
| restart_count | i64 | restarts consumed |
| watchdog_timeout_ms | i64 | 0 disables watchdog |
| last_heartbeat_ms | i64 | last observed heartbeat |
| granted_handles | [text] | device/secret grant ids CURRENTLY HELD |
| state | text | STATE_* below |

## Lifecycle states
`Registered -> Starting -> Ready -> (Degraded | Failed) -> Stopping -> Stopped`,
with a `Restarting` sub-path that re-enters `Starting` after grants are cleared.

## Pure functions (no IO, no syscalls, no extern)
- `can_start(m, ready_set)` — true iff every readiness_dep is in ready_set.
- `mark_starting/mark_ready/mark_stopping/mark_stopped` — explicit transitions.
- `record_heartbeat(m, now)` — feeds watchdog.
- `record_health(m, ok)` — ok=>Ready; !ok: Ready->Degraded then ->Failed.
- `check_watchdog(m, now)` — Ready past `last_heartbeat + watchdog_timeout` => Failed (timeout 0 disables).
- `should_restart(policy, count, max)` — never=>false; else `count < max` (restart-storm bound).
- `on_restart(m)` — **§21 invariant**: returns a copy with `granted_handles = []`, `restart_count+1`, state=Restarting. A restarted service holds ZERO stale grants and must re-acquire from the broker.
- `holds_grants(m)` — true while any grant is still held.

All transitions build through one private `_clone` site (value-type copy), so
functions are pure and the pre-crash manifest is never mutated.

## Relation to driver_supervisor (compat, NOT duplicate)
- `driver_supervisor/supervisor.spl` owns the LIVE restart mechanism (spawn / ping / re-grant) and enforces `MAX_RESTART_ATTEMPTS`; ServiceManifest is the declarative descriptor + pure decision layer a supervisor evaluates (`should_restart` mirrors that cap; `on_restart` encodes the grant-clearing step the supervisor already performs via `pcimgr_release_device`).
- `driver_supervisor/grant_broker.spl` owns grant token issuance/revocation; `granted_handles` holds the ids it issued, and `on_restart` guarantees they are dropped so a respawned service cannot inherit a stale device/secret token.
- Generalizes the ad-hoc per-service `ready()` bools in `src/os/kernel/boot/init_services.spl` into typed `state` + `can_start(readiness_deps, ready_set)`.

## Spec verdict
`11 examples, 0 failures` (5 describe blocks: readiness gating 3, health 2, restart-storm 2, watchdog 2, §21 invariant 2).
Runner: `/tmp/svclane/bin/svcjob` (copy of bin/release/x86_64-unknown-linux-gnu/simple; deployed bin/simple stale/hangs).
Fail-once proof: setting `on_restart` to keep `granted_handles` => the two §21-invariant examples fail (`expected true to equal false`, `expected 1 to equal 0`); reverted to `[]` => green.

## Next increment (resume plan)
1. Wire real services to DECLARE a `ServiceManifest` (start with init_services.spl consumers: clock/vfs/pcimgr/nvme-user) and have the supervisor drive `can_start`/`record_health`/`should_restart`/`on_restart` instead of ad-hoc bools.
2. Bridge `on_restart` to `grant_broker.revoke_driver(name)` so clearing handles in the model triggers real token revocation at restart.
3. Formal Lean proof of the restart-no-stale-grant invariant: `forall m. on_restart(m).granted_handles == []` (and no grant id in the post-restart set appears without a fresh broker issuance). Model alongside the existing service invariants.
4. Add a serial/QEMU evidence scenario showing a supervised driver crash -> restart with grant re-acquisition (board-runnable per board-runnable rule).
