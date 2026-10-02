# Windows parallel process owner research

Issue: https://github.com/ormastes/simple/issues/2188
Selected scope: actual Windows parallel testing with an explicit80-worker request.

The live std async runner refused Windows capture. The app entry then silently disabled parallel. The raw piped owner is unsuitable:16 slots and OS PIDs, while legacy Windows async wait consumes HANDLEs. The in-tree pure-Simple windows_process_owner already supplies UTF16 argv, explicit inherited handles, image pins, JobObjects, poll/cancel/collect and nonreused ownership slots. Reuse this counterpart; no new C runtime is required.

Two additional blockers: the resource governor waited with a fixed active count before the parent could poll/release children, and blocking process-slot acquisition could stop the parent at the automatic64-slot limit. Explicit worker selection must replace automatic defaults while preserving an explicit SIMPLE_MAX_PROCS hard cap.

Microsoft references: [CreateProcessW](https://learn.microsoft.com/en-us/windows/desktop/api/processthreadsapi/nf-processthreadsapi-createprocessw) describes exact application paths and per-process inherited-handle lists. [Job Objects](https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects) documents descendant association and kill-on-close containment.

Verification status: source diagnosis and implementation only; native producer qualification is pending. No Windows concurrency PASS is inferred from source, fixture existence or a bootstrap seed.