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
