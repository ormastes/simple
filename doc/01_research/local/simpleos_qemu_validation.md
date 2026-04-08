<!-- codex-research -->
# SimpleOS QEMU Validation Research

Date: 2026-04-08
Scope: SimpleOS QEMU validation for boot, window manager, browser app surfaces, mouse/input, SSH, and CLI/tools.

## Workspace Notes

- The worktree is dirty. Relevant modified files include:
  - `examples/simple_os/arch/x86_64/wm_entry.spl`
  - `examples/browser/test/compat/chrome_compare.spl`
  - `examples/browser/test/compat/test_manifest.spl`
  - `src/app/ui.web/html.spl`
  - `src/lib/common/web/browser_session.spl`
  - `tools/electron-shell/index.html`
  - `tools/electron-shell/main.js`
- Existing `build/os/` artifacts were present before this validation. Some lanes reused them directly.

## Relevant Runtime Entry Points

### QEMU / boot scripts

- `scripts/os_qemu_test.shs`
  - Headless x86_64 smoke test.
  - Checks serial markers for boot, memory, services, shell, and compositor.
- `scripts/os_gui.shs`
  - GUI desktop launcher.
  - `--wm` switches to `examples/simple_os/arch/x86_64/wm_entry.spl`.
  - `--serial` routes serial to stdout instead of a file.
- `scripts/make_os_disk.shs`
  - Builds `build/os/fat32.img` with fixture files for NVMe/FAT32 lanes.
- `src/os/qemu_runner.spl`
  - Defines target-based `build_os/run_os/test_os`.
  - Also defines named scenarios: `x64-gui`, `x64-desktop-test`, `x64-full-stack`, `x64-ssh`, `x64-nvme-fat32`, `rv64-base`, `rv64-dtb-pci`.

### GUI / browser / input surfaces

- `examples/simple_os/arch/x86_64/gui_entry.spl`
  - Full desktop shell entry with BGA framebuffer + PS/2 keyboard/mouse.
- `examples/simple_os/arch/x86_64/wm_entry.spl`
  - Stable glass window-manager path.
- `src/os/desktop/shell.spl`
  - Desktop shell, launcher integration, app creation, browser demo reachability.
- `src/os/apps/browser_demo/browser_demo.spl`
  - Widget-facing browser app that runs DOM -> CSS -> layout -> paint -> pixels.
- `src/os/apps/browser_sample/browser_sample.spl`
  - Serial-friendly browser pipeline sample with non-background pixel check.
- `src/os/drivers/input/ps2_mouse.spl`
  - PS/2 mouse packet parsing and event generation.
- `src/os/compositor/hosted_input_backend.spl`
  - Hosted path for mouse/keyboard input outside QEMU.

### CLI / tool surfaces

- `src/os/apps/shell/shell_app.spl`
  - Interactive shell with built-ins and extended command dispatch.
- `src/os/tools/shell/register_tools.spl`
  - Small ToolRegistry subset only.
- `examples/simple_os/arch/x86_64/tools_test_entry.spl`
  - Baremetal/QEMU tools validation entry.

### SSH / networking surfaces

- `examples/simple_os/arch/x86_64/ssh_live_entry.spl`
  - Live SSH daemon boot path.
- `examples/simple_os/arch/x86_64/ssh_system_test_entry.spl`
  - SSH system test path.
- `src/os/apps/sshd/sshd.spl`
  - Live daemon implementation.

## Executed QEMU Lanes

### 1. Headless boot smoke

Command:

```sh
sh scripts/os_qemu_test.shs
```

Observed result:

- PASS at the smoke-test level.
- Tier results:
  - Tier 1 PASS: boot banner / serial init
  - Tier 2 PASS: memory initialization
  - Tier 3 PASS: service initialization
  - Tier 4 PASS: shell / main loop
  - Tier 5 PASS: display / compositor
- Serial markers seen:
  - `SimpleOS x86_64 boot`
  - `[BOOT] COM1 serial initialized at 115200 baud`
  - `[BOOT] Heap: 512 MB bump allocator`
  - `[BOOT] PCI: 04 devices found`
  - `[BOOT] FAT32 init failed`
  - `[BOOT] VirtIO-net init failed`
  - `[init] Display: framebuffer initialized`
  - `TEST PASSED`

Important caveat:

- The rebuild reported 4 non-critical parse failures in:
  - `src/os/compositor/browser_compositor_backend.spl`
  - `src/os/compositor/compositor.spl`
  - `src/os/compositor/uart_input_backend.spl`
  - `src/os/gui/shortcut.spl`
- The smoke script still passed because the boot target did not depend on those paths to finish the lane.

Interpretation:

- The x86_64 headless boot lane is healthy enough for serial smoke coverage.
- Storage and networking are not proven by this lane; both failed during init.

### 2. WM / GUI lane

Command:

```sh
timeout 25 sh scripts/os_gui.shs --run-only --wm --serial
```

Observed result:

- QEMU booted the stable WM image `build/os/simpleos_wm_32.elf`.
- Serial markers show framebuffer, PS/2 keyboard, PS/2 mouse, compositor, and desktop shell setup.
- The glass desktop render stage was reached.
- The run later hit a `heap exhausted` panic after entering the shell event loop.

Interpretation:

- The WM path boots far enough to initialize graphics and input and to render the desktop.
- This is not a clean long-running pass; the session degrades after render.
- Mouse interaction was not actually driven end-to-end in QEMU during this run.
- Browser app reachability is present in code, but the browser app itself was not launched in this lane.

### 3. Tools / CLI / NVMe / FAT32 lane

Command:

```sh
timeout 45s qemu-system-x86_64 \
  -machine q35 \
  -cpu qemu64 \
  -m 512M \
  -serial file:build/os/tools_test_serial_20260408_124357.log \
  -display none \
  -no-reboot \
  -drive file=build/os/fat32.img,if=none,id=nvm,format=raw \
  -device nvme,serial=deadbeef,drive=nvm \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -kernel build/os/simpleos_tools_test_x86_64.elf
```

Observed result:

- Guest booted and ran the tools test entry.
- Serial ended with:
  - `Results: 32 passed, 0 failed`
  - `ALL TESTS PASSED`
- Tool groups exercised:
  - filesystem
  - device
  - process
  - network
  - archive
  - boot
  - log
  - package

Critical caveat:

- The harness is permissive.
- In `examples/simple_os/arch/x86_64/tools_test_entry.spl`, `test_run()` marks a tool as pass without checking the return code.
- Serial output shows multiple weak results under an all-pass summary:
  - `lspci` reported `No PCI devices found.`
  - `ifconfig` reported `No network interfaces found.`
  - `ps` and `top` logged `list_tasks failed with code -38`

Interpretation:

- This lane proves the tools test image boots and reaches the full CLI sweep.
- It does not prove device-backed or service-backed correctness of the CLI/tool suite.

### 4. SSH / network lane with unique hostfwd port

Port used:

- Host `2224` -> guest `22`

System-test command:

```sh
qemu-system-x86_64 \
  -machine q35 -cpu qemu64 -m 2G \
  -serial file:build/os/ssh_2224_serial.log \
  -display none -no-reboot \
  -kernel build/os/simpleos_ssh_systest_mb.elf \
  -netdev user,id=n0,hostfwd=tcp::2224-:22 \
  -device virtio-net-pci,netdev=n0 \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04
```

Host probe:

```sh
ssh -vv \
  -o BatchMode=yes \
  -o PreferredAuthentications=none \
  -o PubkeyAuthentication=no \
  -o PasswordAuthentication=no \
  -o StrictHostKeyChecking=no \
  -o UserKnownHostsFile=/tmp/simpleos_known_hosts \
  -o ConnectTimeout=5 \
  -p 2224 root@127.0.0.1 true
```

Observed result:

- Host TCP connect succeeded.
- Guest network initialized and listened on port 22.
- Guest serial markers:
  - `[init] Network stack: OK`
  - `[boot] Network ready`
  - `[tcp] Socket 0 listening on port 22`
  - `[tcp] Connection established on port 22`
  - `[tcp-accept] accepted socket 1`
  - `[PASS] Client connection accepted`
  - `[PASS] Version string sent`
  - `[FAIL] Client SSH version received (>=4 bytes)`
  - `=== SSH System Test Results: 14/15 passed ===`

Interpretation:

- QEMU user networking and hostfwd are working.
- TCP accept is working.
- The SSH system-test path is close but not fully passing.

### 5. Live `sshd` lane

Command:

```sh
qemu-system-x86_64 \
  -machine q35 -cpu qemu64 -m 2G \
  -serial file:build/os/ssh_2224_live_serial.log \
  -display none -no-reboot \
  -kernel build/os/simpleos_ssh_full_mb.elf \
  -netdev user,id=n0,hostfwd=tcp::2224-:22 \
  -device virtio-net-pci,netdev=n0 \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04
```

Observed result:

- Immediate fault:
  - `FAULT @ 0x0000000000000003`
- Host-side SSH reached TCP connect but timed out during banner exchange.
- No daemon-ready marker such as `[sshd] SSH daemon listening on port 22` appeared.

Interpretation:

- Live `SshDaemon` boot is currently broken.
- Networking and hostfwd are not the blocker here; the guest faults before daemon readiness.
- Follow-up artifact analysis tightened the failure:
  - the bootable live multiboot image carries both unresolved early bindings:
    - `U serial_println`
    - `U Users__ormastes__simple__examples__simple_os__arch__x86_64__ssh_live_entry__SshDaemon`
  - source order in `examples/simple_os/arch/x86_64/ssh_live_entry.spl` calls `serial_println(...)` before `SshDaemon.new(22)`
  - the bootable live multiboot image shows early null indirect calls inside `spl_start`
  - strongest current mapping:
    - first null indirect call most likely maps to the first `serial_println("")`
    - second null indirect call most likely maps to the second `serial_println("=== SimpleOS SSH Live Boot ===")`
  - these null calls are the nearest static explanation for the observed `FAULT @ 0x0000000000000003`
  - strongest current reading: unresolved `serial_println` is the first fault edge, while unresolved `SshDaemon` is a later edge the image never reaches
  - the working `ssh_system_test` image has the same early call structure, but all of those targets are concrete non-zero addresses

## Browser / Mouse / GUI Validation Status

### Browser

- Browser app code is wired into the desktop path:
  - `src/os/desktop/shell.spl`
  - `src/os/desktop/app_manifest.spl`
- The QEMU runs above did not prove browser launch or browser rendering inside the actual desktop session.
- The serial-friendly browser sample exists in `src/os/apps/browser_sample/browser_sample.spl` and is a good next isolated lane.
- Follow-up isolation showed the current `browser_sample.spl` path is blocked before runtime:
  - `bin/simple run src/os/apps/browser_sample/browser_sample.spl`
  - failure chain: `browser_sample -> engine2d_executor -> Engine2D -> backend_cuda`
  - concrete parser blocker: `src/std/gc_async_mut/gpu/engine2d/backend_cuda.spl`
  - separate host-run blocker: `unknown extern function: serial_println`
- The architectural blocker is dependency selection, not `browser_sample.spl` syntax.
- The shortest currently viable software-only browser path is not `BrowserRenderer`; it is the direct software pipeline already used by:
  - `src/os/compositor/browser_backend.spl`
  - `src/lib/common/ui/backend_factory.spl`
  - flow: `UITree -> DOM -> layout -> paint -> RenderScene -> execute_scene_to_buffer`
- The most practical next lane is a new baremetal entry such as:
  - `examples/simple_os/arch/x86_64/browser_soft_entry.spl`
- Minimal structure for that lane:
  - build a fixed `BeDomNode` tree
  - run `layout_tree`
  - run `generate_paint_list`
  - run `paint_commands_to_scene`
  - run `execute_scene_to_buffer`
  - count non-background pixels and print strict serial pass/fail markers

### Mouse

- PS/2 mouse init was reached in the WM lane.
- No automated pointer event injection was used yet.
- No end-to-end proof of click, drag, focus, or close behavior exists from this run.
- Follow-up QMP/QOM analysis showed explicit device routing is not available in the current WM VM shape:
  - `ps2-mouse` and `ps2-kbd` exist in the QOM tree
  - but there is no usable QMP device identifier for `input-send-event`
  - explicit device attempts (`video0`, `ps2mouse`, `ps2-kbd`, `i8042`, `VGA`) all returned `DeviceNotFound`
- The guest side is PS/2-only:
  - `examples/simple_os/arch/x86_64/wm_entry.spl` initializes the PS/2 controller directly
  - WM input consumption reads only 3-byte PS/2 auxiliary packets
- The QEMU launch side is also PS/2-only in practice:
  - `scripts/os_gui.shs` uses `-display cocoa` and `-vga std`
  - `src/os/qemu_runner.spl` uses the same GUI shape
  - neither path provisions `usb-tablet`, `virtio-tablet-pci`, or another explicit pointer device
- Generic `input-send-event` and HMP mouse commands were accepted by QEMU but still produced no guest-visible click markers.
- Practical result: reliable automated mouse interaction is not currently proven feasible in this VM shape.
- The narrowest host-side experiment is adding an explicit tablet device, but that is only diagnostic unless the guest also gains a matching input path.
- Best first diagnostic:
  - add `-device usb-tablet` to the WM launch and expose QMP
  - if that still yields no guest-visible pointer activity, stop spending time on QMP routing and move to guest-side input work

### Desktop app launch

- `src/os/test/desktop_e2e_test.spl` exists and should be run as its own lane.
- This validation session did not execute that entry.
- Follow-up work narrowed the blocker:
  - direct harness build can be produced, but QEMU rejects it as a kernel image:
    - `Error loading uncompressed kernel without PVH ELF Note`
  - the smallest bootable wrapper path reaches the x86_64 stub handoff and then dies with:
    - `[PANIC] heap exhausted`
  - so there is still no bootable lane that both wraps the real desktop E2E harness and reaches `test_main()`
- The narrowest concrete cause proven so far is the fixed 64 MB bump heap in:
  - `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- Changing guest RAM from 512 MB to 2 GB does not move the failure point.
- Best current culprit chain:
  - `_start() -> spl_start() -> generated wrapper / entry-closure setup -> early runtime string/array/map allocations`
- `scripts/run_os_tests.shs` compiles tests with `--entry-closure`, which is now the strongest wrapper-level suspect for this early allocation burst.
- Refined reading:
  - `launcher_init()` itself is mostly static-state mutation
  - the stronger current suspects are wrapper-generated `serial_println` formatting and entry-closure runtime object materialization before the launcher path begins
- Static evidence in the bootable wrapper:
  - long literal-byte string construction sequences appear in `build/os/desktop_e2e_boot.elf` before the first meaningful launcher work
  - the image is stripped, so symbol-level mapping is limited without instrumentation

## Current Conclusions

### Proven working enough

- Headless x86_64 boot smoke.
- WM/GUI boot to render stage.
- Tools/NVMe/FAT32 lane boot and broad CLI dispatch.
- QEMU user networking plus hostfwd on a unique port.
- SSH system-test path up to TCP accept.

### Proven broken or incomplete

- Live `sshd` lane faults immediately.
- WM/GUI lane is not stable after entering the event loop (`heap exhausted`).
- Tools test harness over-reports success.
- Browser rendering inside the desktop session is not proven.
- Mouse interaction is initialized but not end-to-end verified.
- The live `sshd` failure is now isolated to the entry-wrapper / artifact layer:
  - the working system-test image has concrete early bindings
  - the failing live image carries unresolved early imports
  - disassembly shows the live path making early null indirect calls inside `spl_start`
- The browser sample path is blocked by unconditional `Engine2D` / `backend_cuda` imports before backend fallback can help.
- The next browser lane is concrete enough to implement:
  - new entry `examples/simple_os/arch/x86_64/browser_soft_entry.spl`
  - imports only `BeDomNode`, `layout_tree`, `generate_paint_list`, `paint_commands_to_scene`, and `execute_scene_to_buffer`
  - validates success by counting non-background pixels in a software-rendered buffer

## Immediate Next Validation Targets

1. Debug the x86_64 wrapper path for `desktop_e2e_test.spl`, starting from pre-`test_main()` allocation bursts inside the fixed bump heap.
2. Build a browser QEMU lane around the direct software browser pipeline instead of `BrowserRenderer` / `Engine2D`.
3. Either change the WM input backend / VM shape to something QMP-routable, or instrument the guest to prove whether generic injected events arrive at all.
4. Tighten `tools_test_entry.spl` so `test_run()` respects return codes.
5. Fix the live SSH entry/artifact path so both `serial_println` and `ssh_live_entry__SshDaemon` are resolved and early `spl_start` calls are non-null.
