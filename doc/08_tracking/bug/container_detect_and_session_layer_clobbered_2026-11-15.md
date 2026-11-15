# Container-detect modules and OCap session layer lost to broad commits (2026-11-15)

Status: FIXED on `work/container-detect-multitenant-20261115` (base origin/release/1.0.0).

## 1. container_detect specs import deleted modules
- `test/03_system/gui/container_detect_spec.spl:30,35` and `test/system/gui/container_detect_spec.spl:30,35`
  import `common.test_runner.display_detect` and `common.ui.backend_factory`.
- Both deleted by broad commit `2cca0bc59c4` ("Track production readiness convergence",
  -16,573 lines, all of `src/lib/common/ui/`). No successor module exists (searched for
  `create_backend` / `detect_display`). Restored verbatim from `2cca0bc59c4~1`; their
  dependencies (`app.ui.{none,tui,web,tauri}.*`, `os.compositor.browser_backend`) still resolve.

## 2. container_multitenant spec: API "missing"
- The API was not new: `login`, `create_child_session`, `open_subrole`,
  `bind_task_to_session`, `session_teardown`, `session_of`, `create_container`,
  `container_live`, `escrow_cap`, `consume_escrow`, `open_system`, `create_child_quota`
  existed in `src/os/kernel/ipc/capability.spl` at `e274cd33719~1` and were dropped by a
  stale-snapshot merge (`e274cd33719` lineage). `session_types.spl` (Session/Container/EscrowCap)
  survived unchanged.
- Fix: restored the session/container/escrow/multi-tenant block, the session table fields,
  and the S3 session-liveness gate in `check()`; marked `capset_subset` /
  `capset_clone_unpledged` `pub` (seed now enforces cross-module visibility).
- Also fixes `session_hierarchy_spec`, which was red for the same reason.

## Still-open (not restored, owner decision)
Same diff vs `e274cd33719~1` shows other security hardening dropped from `capability.spl`:
`check_file_access` per-perm capability checks, pledge-to-empty `is_pledged` fixes in
revoke paths, `init_task` ambient-full → empty clamp, token_id/depth on sandbox-lowering
tokens, and `_path_starts_with` component-boundary check. Needs its own review.

## Evidence
container_detect (both trees) 19/19; container_multitenant 17/17; session_hierarchy 19/19;
adversarial_revocation_soundness 5/5; spawn_with_cspace 17/17.
