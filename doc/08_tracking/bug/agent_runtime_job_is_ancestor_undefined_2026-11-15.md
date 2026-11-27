# `Scheduler.job_is_ancestor` called but defined nowhere (2026-11-15)

**Status:** FIXED

`src/os/security/llm_profiles/agent_runtime.spl` (`terminate_agent_subtree`)
called `scheduler.job_is_ancestor(controller_job, target_job)`, which existed
nowhere. Implemented as `sched_job_is_ancestor` in
`src/os/kernel/scheduler/authority_runtime.spl` (walks task-owned
`TaskSecurity.parent_job_id` links, strict, bounded by task count) plus the
`Scheduler.job_is_ancestor` method in `_Scheduler/scheduler_authority.spl`.
`live_job_member_ids` / `terminate_job` already exist on base (PR #9272).

Spec: `test/01_unit/os/kernel/scheduler/scheduler_job_is_ancestor_spec.spl`.

## Related: agent launch fixture returned -13 (EACCES)

`test/01_unit/os/security/agent_runtime_spec.spl` launch case failed with
`-13`. Root cause: `exec_cap_check_caps` in
`fs_exec_adopt_authenticated_with_launch_v1`
(`src/os/kernel/loader/fs_exec_spawn.spl`) correctly denied the fixture's
image path `/workspace/agent.smf`, which lies outside the
`SPAWN_RECIPE_APP_LAUNCHER` parent's FileExec root `/sys/apps/`. The kernel is
right; the fixture was wrong. Fixed in the spec (`/sys/apps/agent`, plus the
host-arch ELF fixture like `container_runtime_spec`). Note the emergency-stop
case was vacuous before (guarded by `if launched.pid > 0`); it now exercises
`terminate_agent_subtree` for real. 4/4 pass.
