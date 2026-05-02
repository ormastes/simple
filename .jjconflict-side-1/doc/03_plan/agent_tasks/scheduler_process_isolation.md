<!-- codex-design -->
# Agent Tasks: Scheduler + Process Isolation

1. Extend task and scheduler data structures.
2. Wire enqueue/remove/schedule around per-CPU class queues.
3. Expose `sys_schedule` and `sys_schedctl` handlers and C-ABI shims.
4. Extend `@task` parser and validation helpers.
5. Add focused unit tests and run scheduler/compiler verification subsets.
