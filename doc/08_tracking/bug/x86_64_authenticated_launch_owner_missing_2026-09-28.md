# x86_64 authenticated launch owner does not carry argv into execution

**Status:** open. **Inspected:** `origin/main` at `e2dab431827` on
2026-09-28. **Scope:** x86_64 SimpleOS authenticated filesystem execution and
terminal scheduler evidence.

`authenticated_fs_exec_submission_service_v1.spl` imports and calls
`x86_64_fs_exec_spawn_authenticated_with_launch_v1`, but
`x86_64_fs_exec_spawn.spl` does not define it. Adding a facade that validates
argv and then calls `fs_exec_adopt_authenticated_v1` would not complete the
route: that bridge passes no argv or envp to
`Scheduler.adopt_authenticated_executable_pid_v1`. The scheduler calls
`executable_prepare_image_v1`, which builds the user image with empty vectors,
and records adoption through `scheduler_execution_observe_adoption_v1` without
an observed command. The terminal
`scheduler_execution_compare_and_deliver_reaped_v2` requires a command
observation and exact path/argv match before issuing evidence.

The x86_64 launch owner must validate and retain one
`ExecutableLaunchArgumentsV1`, bind it to the admitted executable path and
recipe, pass its argv/envp into the mapped initial user stack, and record the
same owned launch in the scheduler observation before publication. The
one-shot executable authority, capability attenuation, child exit/reap, and
terminal evidence must remain one transaction. A source-only facade that
reports the caller's argv after a path-only adoption would make a false
execution claim.

Acceptance requires source-matched pure-Simple checks of the actual x86_64
closure and a guest execution proving argv/envp received by the child. Reject
invalid launch strings, recipe/path mismatch, inadequate caller capabilities,
stale/replayed authority, command mismatch, and incomplete reap without
terminal evidence. This remains a release blocker until those checks pass.
