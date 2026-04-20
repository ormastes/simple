# SimpleOS Syscall 13 Direct Handoff Todo (2026-04-20)

## Scope

Finish `FR-SOS-024`: packaged apps must launch from mounted filesystem bytes as
scheduler-owned user processes instead of resident-manifest compatibility
windows.

## Current Evidence

The x64 desktop disk lane now proves:

- FAT32/VFS resolves packaged app paths such as `/sys/apps/browser_demo`.
- syscall 13 copies executable bytes into owned loader storage.
- `build_user_process_image` succeeds for Browser Demo, Hello World, and Editor.
- Direct QEMU memory bootstrap initializes PMM/VMM before app launch.
- A diagnostic direct handoff reached address-space creation, image mapping,
  TCB construction/storage, and capability registration.
- The live lane remains QEMU green through resident fallback:
  `[syscall13] user image handoff gated; scheduler enqueue pending` followed by
  `TEST PASSED`.

## Remaining Work

- [ ] Fix scheduler runqueue enqueue from syscall/trap context. Diagnostic runs
      reached capability registration and stalled before `_enqueue_ready` could
      enter.
- [ ] Preserve the resident-manifest fallback for unsupported images and
      manifest-only apps, but make process-backed apps fail tests if direct
      handoff regresses.
- [ ] Wire the x86_64 scheduler/trap return path so a newly created task's
      `user_context` can be entered safely at ring 3.
- [ ] Add QEMU/system coverage that asserts process-backed PIDs for Browser
      Demo, Hello World, and Editor.
- [ ] Add negative coverage proving resident fallback still works when syscall
      13 returns an expected unsupported-image error.
- [ ] Remove the syscall 13 gate in `_spawn_from_resolved_bytes` only after the
      desktop disk lane reaches `TEST PASSED` without resident fallback markers.

## Acceptance Markers

Required live serial markers:

- `[syscall13] build_user_process_image ok`
- `[syscall13] user image handoff ok`
- `[desktop-e2e] process-backed:yes app=browser_demo`
- `[desktop-e2e] process-backed:yes app=hello_world`
- `[desktop-e2e] process-backed:yes app=editor`
- `TEST PASSED`

Forbidden live serial markers for the direct process-backed case:

- `resident-manifest`
- `process-backed:unknown`
- `EXCEPTION`
- `FAULT @`
- `cr2=`
- `cr3=`
- `heap exhausted`
- `PANIC`

## References

- Feature request: `doc/08_tracking/feature_request/simpleos_os_requests.md`
  (`FR-SOS-024`)
- Status report:
  `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md`
- Architecture:
  `doc/04_architecture/scheduler_process_isolation.md`
- Guide:
  `doc/07_guide/platform/sosix_process_scheduler.md`
