# SimpleOS ARM64 WM QEMU Verification

This lane verifies the canonical Simple ARM64 Engine2D desktop entry under
`qemu-system-aarch64` with QEMU `ramfb`.

## Build

Use an LLVM-enabled pure-Simple self-hosted release driver. The Rust driver is
bootstrap-only and is not a verification fallback. On Apple Silicon, set:

```bash
SIMPLE=bin/release/aarch64-apple-darwin/simple
test -x "$SIMPLE"
```

Build the WM kernel:

```bash
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=src SIMPLE_ALLOW_FREESTANDING_STUBS=1 \
LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18 \
PATH=/opt/homebrew/opt/llvm@18/bin:$PATH \
LIBRARY_PATH=/opt/homebrew/opt/zstd/lib:$LIBRARY_PATH \
"$SIMPLE" native-build \
  --source build/os/generated --source src/os --source src/lib --source examples/09_embedded/simple_os \
  --backend llvm --opt-level=aggressive --log on --timeout 180 \
  --entry-closure --entry examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl \
  --target aarch64-unknown-none \
  -o build/os/simpleos_arm64_wm.elf \
  --linker-script examples/09_embedded/simple_os/arch/arm64/linker.ld
```

## Run

On Apple Silicon, use HVF with `-cpu host`:

```bash
qemu-system-aarch64 \
  -machine virt -cpu host -accel hvf -m 384M \
  -serial file:build/os/arm64_wm_serial.log \
  -display none -no-reboot \
  -kernel build/os/simpleos_arm64_wm.elf \
  -device ramfb
```

On Linux hosts that are not ARM64/KVM, use TCG with an emulated ARMv8 CPU:

```bash
qemu-system-aarch64 \
  -machine virt -cpu cortex-a57 -accel tcg -m 384M \
  -serial file:build/os/arm64_wm_serial.log \
  -display none -no-reboot \
  -kernel build/os/simpleos_arm64_wm.elf \
  -device ramfb
```

On Linux ARM64 hosts with `/dev/kvm`, use `-accel kvm -cpu host` instead.

## Host Readiness Probe

Before attempting the full build and boot, check that the host QEMU binary
supports the documented `virt` plus `ramfb` lane:

```bash
sh scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs
```

The probe verifies that `qemu-system-aarch64` is on `PATH`, that the `virt`
machine and `ramfb` device are available, and that QEMU accepts the documented
headless `virt`/`ramfb` dry-run command for the current host accelerator:
`hvf` on Darwin, `kvm` on Linux ARM64 with `/dev/kvm`, otherwise `tcg` with
`cortex-a57`. It is not a live boot proof; the serial markers below remain the
acceptance signal for a completed ARM64 WM run.

## Runner Scenario Contract

The repo QEMU runner exposes the same lane as the named scenario
`arm64-wm-ramfb`. The scenario resolves to `get_arm64_wm_qemu_target()` and
builds/runs:

```text
examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl
build/os/simpleos_arm64_wm.elf
qemu-system-aarch64 -machine virt -cpu <host|cortex-a57> -accel <hvf|tcg> -m 384M -kernel build/os/simpleos_arm64_wm.elf -device ramfb
```

The runner selects HVF/`host` on Apple Silicon and portable TCG/`cortex-a57`
otherwise. The separate readiness script may select KVM on a capable Linux
ARM64 host. This build/run command contract does not replace the serial-marker
acceptance gate below or claim that the kernel currently boots to a rendered
frame.

## Runner CLI Contract

Use the named scenario when driving this lane through the SimpleOS runner:

```bash
bin/simple os build --scenario=arm64-wm-ramfb
bin/simple os run --scenario=arm64-wm-ramfb
bin/simple os test --scenario=arm64-wm-ramfb
```

The test command is a live acceptance attempt. It should be considered passing
only when `build/os/arm64_wm_serial.log` contains every acceptance marker
listed below. The runner uses a persistent serial file for this lane so a guest
that reaches the WM markers and then keeps running is still usable evidence;
scenario wiring and command construction alone are not boot evidence.

The WM RAMFB lane above and the dedicated desktop scenario both select the
canonical Engine2D desktop entry while retaining their distinct output and
QEMU launch contracts:

```bash
bin/simple os build --scenario=arm64-desktop-engine2d
bin/simple os run --scenario=arm64-desktop-engine2d
bin/simple os test --scenario=arm64-desktop-engine2d
```

It builds `arch/arm64/gui_entry_desktop.spl` with the `src/os` and `src/lib`
closure, configures RAMFB, and renders compositor-owned Simple Web content via
`DesktopShell` and `Engine2dWmFrameExecutor`. The static scenario intentionally
does not invent a shared-memory path or daemon lifecycle.
RAMFB fw_cfg DMA is owned by `src/os/kernel/arch/arm64/ramfb.spl`; PL011 input
is owned by the ARM64 console over the shared PL011 MMIO helper. The canonical
desktop imports those architecture facades and the shared shortcut mapper, not
the legacy `wm_entry_io.spl` glass-demo runtime closure.
The guest is a persistent desktop, so `os run` and `os test` accept its timeout
only when the captured serial output contains RAMFB configuration, the
canonical first-frame marker emitted after a positive revision, and the ARM
desktop-ready marker. This proves local Engine2D composition, not host-GPU
execution.

The host-GPU evidence owner remains
`scripts/check/check-simpleos-qemu-host-gpu-2d.shs`. Its AArch64 row must first
pass the existing 64x48 raw-render, Draw IR, and independent ProcessingIR probe.
It then boots `arm64-desktop-engine2d` as a second guest while reusing the same
host daemon, 8 MiB shared-memory file, and maximum-RSS monitor. The production
QEMU argument evidence must name the desktop ELF and exact ARM `virt`,
`cortex-a72`, 512 MiB memory, `-nographic`, `ramfb`, `virtio-net-pci`,
`memory-backend-file,id=hostgpu,share=on,mem-path=<row-shm>,size=8M`, and
`ivshmem-plain,memdev=hostgpu` tokens in that order; the shared-memory path must
be the same one used by the probe and no extra argument is admitted. The
production ready generation must continue from the probe's final ProcessingIR
generation: plus one for Metal, plus two for DirectX, or plus three for Vulkan,
matching the executor's Metal, DirectX, then Vulkan negotiation order.

That wrapper row passes only when RAMFB configures and the serial stream orders
the correlated production markers:

```text
[wm-frame] host-gpu-ready backend=<host-backend> generation=<ready>
[wm-frame] host-gpu-presented backend=<host-backend> generation=<ready+1> run=<ready> frame=<ready+1> checksum=<positive>
[desktop-gui] first-frame-rendered scene_revision=<positive>
[desktop-gui-arm64] desktop-ready revision=<same-positive-revision>
```

This production gate is additive: it never substitutes for the 64x48
ProcessingIR receipt. TODO 548 still prevents a fresh compiler build and QEMU
execution, so the wrapper contract is source-level and no fresh live PASS is
claimed. Cached wrapper reports without the AArch64 production serial-log and
production-argv evidence keys are invalid and must fail `--validate-report`.

`test/03_system/gui/arm64_wm_ramfb_screendump_spec.spl` is the focused framebuffer
proof target for this lane. It reuses the repo QMP harness, waits for
`[desktop-gui-arm64] desktop-ready revision=`, requests a QMP `screendump`, validates the PPM
header, and asserts that a real framebuffer image was produced. If the ARM64
native build is blocked, this spec writes
`build/os/arm64_wm_ramfb_screendump.blocker.txt` before any framebuffer claim
can be made.

## Acceptance Markers

The serial log must include:

```text
[desktop-gui-arm64] boot
[WM] fw_cfg sig: 81 69 77 85
[WM] Found etc/ramfb in fw_cfg
[WM] ramfb configured successfully via fw_cfg DMA
[desktop-gui-arm64] desktop-ready revision=<positive>
```

Notes:
- QEMU `virt` fw_cfg MMIO is accessed at `0x09020000`.
- `ramfb` uses fw_cfg selector discovery for `etc/ramfb`, then writes the
  framebuffer descriptor with fw_cfg DMA.
- The ARM64 verification path renders compositor-owned surfaces through
  `DesktopShell` and `Engine2dWmFrameExecutor`.
