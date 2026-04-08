# SimpleOS QEMU Validation Plan

Date: 2026-04-08
Goal: validate SimpleOS end-to-end across boot, WM/GUI, browser surfaces, mouse input, CLI/tools, and SSH/networking using separate QEMU lanes.

## Completed Lanes

1. Headless boot smoke
   - Status: PASS
   - Command: `sh scripts/os_qemu_test.shs`
   - Evidence: serial tier checks all passed.

2. WM / GUI boot
   - Status: PARTIAL
   - Command: `timeout 25 sh scripts/os_gui.shs --run-only --wm --serial`
   - Evidence: framebuffer, PS/2 keyboard, PS/2 mouse, compositor, desktop shell, glass desktop render.
   - Failure: heap exhaustion after event loop entry.

3. Tools / NVMe / FAT32
   - Status: PARTIAL
   - Command: custom `qemu-system-x86_64` with `build/os/simpleos_tools_test_x86_64.elf` and `build/os/fat32.img`
   - Evidence: `32 passed, 0 failed`
   - Failure: harness does not check actual tool return codes.

4. SSH system test
   - Status: PARTIAL
   - Host port: `2224`
   - Evidence: TCP connect, guest accept, `14/15 passed`
   - Failure: client SSH version read is not fully passing.

5. Live `sshd`
   - Status: FAIL
   - Host port: `2224`
   - Evidence: immediate `FAULT @ 0x0000000000000003`

## Remaining Lanes

### P0

1. Desktop launcher integration lane
   - Entry: `src/os/test/desktop_e2e_test.spl`
   - QEMU shape: `x64-desktop-test`
   - Purpose:
     - prove launcher init
     - prove shortcut dispatch
     - prove WM notification path
   - Pass signals:
     - `TEST PASSED`
     - launcher registry count >= 3
     - successful shortcut dispatch
   - Current blocker:
     - direct harness image is not accepted by QEMU as a kernel image
     - smallest bootable wrapper still dies with `heap exhausted` before `test_main()`
     - current best hypothesis is pre-`test_main()` wrapper/runtime allocation burst against the fixed 64 MB bump heap
     - `--entry-closure` compilation is now the strongest wrapper-level suspect
     - strongest current suspects are wrapper-generated `serial_println` formatting and early runtime object materialization, not `launcher_init()` itself

2. Browser sample lane
   - Entry: new baremetal software-render lane, likely `examples/simple_os/arch/x86_64/browser_soft_entry.spl`
   - QEMU shape: headless x86_64 serial lane
   - Purpose:
     - prove DOM -> layout -> paint -> scene -> pixels
     - prove non-background pixels > 0
   - Pass signals:
     - `Rendering complete - pipeline produced visible output`
     - `TEST PASSED`
   - Current blocker:
     - current `browser_sample.spl` path imports `Engine2D`, which unconditionally imports `backend_cuda`
     - `backend_cuda.spl` parse failure prevents a runnable lane
   - Revised approach:
     - use the direct software browser pipeline from `browser_backend.spl` / `backend_factory.spl`
     - avoid `BrowserRenderer.create(...)` and all `Engine2D` imports entirely

3. WM mouse automation lane
   - Entry: `examples/simple_os/arch/x86_64/wm_entry.spl`
   - QEMU shape:
     - GUI enabled
     - QMP socket enabled
   - Purpose:
     - inject pointer move
     - inject click-to-focus
     - inject drag on title bar
      - inject close/minimize click if coordinates are known
   - Pass signals:
      - no crash during interaction window
      - window movement/focus markers in serial or screenshot evidence
   - Current blocker:
     - guest WM code is PS/2-only
     - QEMU GUI launch does not provision an explicit tablet/pointer device
     - explicit QMP device routing is unavailable in this VM shape
     - generic `input-send-event` is accepted by QEMU but does not yield guest-visible clicks
   - Next experiment:
     - add `-device usb-tablet` as the first diagnostic
     - if clicks still do not arrive, shift focus to guest-side input support instead of more QMP routing work

4. Live `sshd` fault isolation lane
   - Entry: live SSH daemon path
   - QEMU shape:
     - headless
     - hostfwd on a unique port
   - Purpose:
     - move from immediate fault to daemon-ready state
   - Pass signals:
     - `[sshd] SSH daemon listening on port 22`
     - banner exchange proceeds beyond TCP connect
   - Current blocker:
     - live multiboot image carries unresolved early bindings
     - fault occurs before first serial print
     - earliest unresolved edge is `serial_println`
     - `ssh_live_entry__SshDaemon` is also unresolved, but later
     - disassembly now confirms early null indirect calls inside `spl_start`
     - strongest current mapping is that the first two null indirect calls correspond to the opening `serial_println(...)` calls in `ssh_live_entry.spl`

### P1

5. Browser launch from desktop lane
   - Entry: full desktop shell path
   - Purpose:
     - prove Browser Demo is not only present in manifests but launchable inside the desktop
   - Pass signals:
     - browser app launch marker
     - browser render marker or browser window creation marker
   - Dependency:
     - lower-level browser software-render lane must exist first

6. Tools harness hardening
   - File: `examples/simple_os/arch/x86_64/tools_test_entry.spl`
   - Purpose:
     - make `test_run()` fail on non-zero tool return codes
   - Pass signals:
     - negative tool paths fail the lane
     - all-pass summary becomes meaningful

7. Headless full-stack lane
   - Scenario: `x64-full-stack`
   - Purpose:
     - combine storage + network + GPU presence in one lane
   - Pass signals:
     - no early subsystem fault
     - storage and network init both succeed

### P2

8. Multi-arch smoke
   - Command: `bin/simple os test --all`
   - Purpose:
     - validate the generic multi-arch QEMU runner
   - Pass signals:
     - reproducible build/run behavior per arch
   - Caveat:
     - non-x86 GUI is not expected to pass.

## Agent Split

1. Agent A: headless / desktop serial lanes
   - desktop E2E
   - browser sample

2. Agent B: GUI / WM interaction lanes
   - WM boot
   - QMP input injection
   - screenshot capture if available

3. Agent C: storage / tools lanes
   - tools_test entry
   - harness hardening follow-up

4. Agent D: networking / SSH lanes
   - SSH system test
   - live `sshd`
   - unique hostfwd ports `2224+`

## Port and Artifact Rules

1. Use a unique host SSH port per network lane.
   - `2224`, `2225`, `2226`, ...
2. Use a unique serial log per lane.
3. Use a unique QMP socket per GUI automation lane.
4. Reuse `build/os/fat32.img` only when the lane does not mutate it; otherwise copy it first.

## Exit Criteria

1. A bootable wrapper for `desktop_e2e_test.spl` reaches `test_main()` and passes in QEMU.
2. A browser software-render lane passes in QEMU without touching `Engine2D` / `backend_cuda`.
3. WM lane either supports provable automated input, or the repo has a different routable GUI lane selected for automation.
4. Live `sshd` image is rebuilt without unresolved early bindings, with non-null early `spl_start` calls, and reaches listening state.
5. Tools lane reports meaningful pass/fail based on real tool exit codes.
