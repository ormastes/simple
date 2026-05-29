# SimpleOS ARM64 WM QEMU Verification

This lane verifies the pure Simple ARM64 glass window manager entry under
`qemu-system-aarch64` with QEMU `ramfb`.

## Build

Use an LLVM-enabled Simple driver. On macOS with Homebrew LLVM 18:

```bash
LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18 \
PATH=/opt/homebrew/opt/llvm@18/bin:$PATH \
LIBRARY_PATH=/opt/homebrew/opt/zstd/lib:$LIBRARY_PATH \
cargo build --manifest-path src/compiler_rust/Cargo.toml \
  -p simple-driver --features llvm
```

Build the WM kernel:

```bash
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=src SIMPLE_ALLOW_FREESTANDING_STUBS=1 \
LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18 \
PATH=/opt/homebrew/opt/llvm@18/bin:$PATH \
LIBRARY_PATH=/opt/homebrew/opt/zstd/lib:$LIBRARY_PATH \
src/compiler_rust/target/debug/simple native-build \
  --source build/os/generated --source src/os --source examples/simple_os \
  --backend llvm --opt-level=aggressive --log on --timeout 180 \
  --entry-closure --entry examples/simple_os/arch/arm64/wm_entry.spl \
  --target aarch64-unknown-none \
  -o build/os/simpleos_arm64_wm.elf \
  --linker-script examples/simple_os/arch/arm64/linker.ld
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

## Host Readiness Probe

Before attempting the full build and boot, check that the host QEMU binary
supports the documented `virt` plus `ramfb` lane:

```bash
sh scripts/check-simpleos-arm64-wm-qemu-readiness.shs
```

The probe verifies that `qemu-system-aarch64` is on `PATH`, that the `virt`
machine and `ramfb` device are available, and that QEMU accepts the documented
headless `virt`/`ramfb` dry-run command. It is not a live boot proof; the serial
markers below remain the acceptance signal for a completed ARM64 WM run.

## Runner Scenario Contract

The repo QEMU runner exposes the same lane as the named scenario
`arm64-wm-ramfb`. The scenario resolves to `get_arm64_wm_qemu_target()` and
builds/runs:

```text
examples/simple_os/arch/arm64/wm_entry.spl
build/os/simpleos_arm64_wm.elf
qemu-system-aarch64 -machine virt -cpu max -m 384M -kernel build/os/simpleos_arm64_wm.elf -device ramfb
```

This is a build/run command contract for the existing scenario machinery. It
does not replace the serial-marker acceptance gate below and does not claim
that the ARM64 WM kernel currently boots to a rendered frame.

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

`test/system/gui/arm64_wm_ramfb_screendump_spec.spl` is the focused framebuffer
proof target for this lane. It reuses the repo QMP harness, waits for
`[WM] Glass desktop rendered!`, requests a QMP `screendump`, decodes the PPM,
and asserts that a real framebuffer image was produced. If the ARM64 native
build is blocked, this spec writes
`build/os/arm64_wm_ramfb_screendump.blocker.txt` before any framebuffer claim
can be made.

## Acceptance Markers

The serial log must include:

```text
[WM] Framebuffer allocated and registered
[WM] fw_cfg sig: 81 69 77 85
[WM] Found etc/ramfb in fw_cfg
[WM] ramfb configured successfully via fw_cfg DMA
[WM] Glass desktop rendered!
[WM] Controls (UART): Tab=cycle, 1/2/3=focus, t=theme, m=minimize, r=restore, q=quit
```

Notes:
- QEMU `virt` fw_cfg MMIO is accessed at `0x09020000`.
- `ramfb` uses fw_cfg selector discovery for `etc/ramfb`, then writes the
  framebuffer descriptor with fw_cfg DMA.
- The ARM64 verification path keeps the WM in Simple and uses direct bar/dock
  drawing primitives so the QEMU render lane does not depend on the layout
  engine.
