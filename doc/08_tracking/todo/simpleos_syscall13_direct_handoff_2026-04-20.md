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

- [x] Fix scheduler runqueue enqueue from syscall/trap context. Diagnostic runs
      reached capability registration and stalled before `_enqueue_ready` could
      enter. Fixed by commit `70b86c97` (enqueue path unblocked) and
      `a3f4f666` (scheduler module global for task ID counter).
- [x] Preserve the resident-manifest fallback for unsupported images and
      manifest-only apps, but make process-backed apps fail tests if direct
      handoff regresses. Launcher scanner fix in `a3f4f666` maintains
      fallback while exposing `process-backed:ok` markers for real app PIDs.
- [x] Wire the x86_64 scheduler/trap return path so a newly created task's
      `user_context` can be entered safely at ring 3. Commit `4708c2c9`
      added `arch_x86_64_enter_user_first`; `a3f4f666` wired syscall 14
      (EnterUserBlocking) end-to-end through
      `dispatch_enter_user_blocking` → `arch_x86_64_enter_user_task`.
- [ ] Add QEMU/system coverage that asserts process-backed PIDs for Browser
      Demo, Hello World, and Editor. Test scaffolding exists; full coverage
      blocked by the stub-collision compiler fix.
- [ ] Add negative coverage proving resident fallback still works when syscall
      13 returns an expected unsupported-image error.
- [ ] Remove the syscall 13 gate in `_spawn_from_resolved_bytes` only after the
      desktop disk lane reaches `TEST PASSED` without resident fallback markers.

## Acceptance Markers

Required live serial markers:

- `[syscall13] build_user_process_image ok`
- `[syscall13] user image handoff ok`
- `[desktop-e2e] process-backed:ok app=browser_demo` (marker form confirmed
  in pre-blocker live run; marker text uses `ok` not `yes`)
- `[desktop-e2e] process-backed:ok app=hello_world`
- `[desktop-e2e] process-backed:ok app=editor`
- `TEST PASSED`

Pre-blocker live evidence (x86_64 desktop disk lane, commit `a3f4f666`):

- `[desktop-e2e] process-backed:ok app=browser_demo pid=1` — confirmed
- `[desktop-e2e] process-backed:ok app=hello_world pid=2` — confirmed
- `[desktop-e2e] process-backed:ok app=editor pid=3` — confirmed
- `mode=filesystem-process`, `editor-save:ok`, `cli-verify:ok` — confirmed
- `TEST PASSED`, 0 faults — confirmed

Forbidden live serial markers for the direct process-backed case:

- `resident-manifest`
- `process-backed:unknown`
- `EXCEPTION`
- `FAULT @`
- `cr2=`
- `cr3=`
- `heap exhausted`
- `PANIC`

## Residual Blockers

### Compiler freestanding-stub symbol-weakness collision

A compiler-level bug causes symbol-weakness collisions in freestanding
(baremetal) builds. Symptom: syscall shim or OS dispatch symbols defined in
the Simple source tree are shadowed by weak stubs from `baremetal_stubs.c`,
causing dispatcher calls to return `-ENOSYS` or silently no-op instead of
routing to the real handler.

- **Owner:** parallel Codex compiler agent (fix in
  `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`).
- **Impact on this tracking item:** blocks live QEMU re-verification against
  HEAD. The pre-blocker live run (commit `a3f4f666`) proves the OS-side
  code is correct; the fix is purely in the compiler toolchain.
- **Separate tracking:**
  `doc/08_tracking/todo/simpleos_stub_collision_freestanding_2026-04-21.md`
- **No OS source changes needed** once the compiler fix lands.

## References

- Feature request: `doc/08_tracking/feature_request/simpleos_os_requests.md`
  (`FR-SOS-024`)
- Status report:
  `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md`
- Architecture:
  `doc/04_architecture/scheduler_process_isolation.md`
- Guide:
  `doc/07_guide/platform/sosix_process_scheduler.md`
