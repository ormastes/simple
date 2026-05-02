<!-- codex-design -->
# System Test Plan: Scheduler + Process Isolation

- Verify existing scheduler QEMU priority markers still pass.
- Add unit coverage for per-CPU queue initialization, fair virtual-deadline ordering, scheduler policy update, schedctl rejection of direct deadline activation, and schedctl deadline admission.
- Add compiler unit coverage for `@task` scheduler policy parsing and RT/deadline runtime-family validation.
- Add future QEMU serial markers for SMP CPU run-queue transitions once AP bring-up executes real tasks.
