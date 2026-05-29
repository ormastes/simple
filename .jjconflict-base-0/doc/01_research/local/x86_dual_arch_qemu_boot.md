<!-- codex-research -->
# Local Research: x86 Dual-Arch QEMU Boot

## Scope

Plan a stable x86 strategy that supports:

- x86_32 boot and validation
- x86_64 boot and validation
- explicit CPU/QEMU differences per lane
- shared browser and desktop app logic without forcing one runtime ABI onto the other

## Repo-Local Findings

### Existing x86_32 lane

- `src/os/kernel/arch/x86_32/boot.spl` is a real Multiboot1 boot layer with memory-map and framebuffer parsing.
- `src/os/kernel/arch/x86_32/console.spl` provides a native COM1 serial path.
- `src/os/qemu_runner.spl` already maps `Architecture.X86` to:
  - `qemu-system-i386`
  - `-machine pc`
  - `-cpu qemu32`
- `examples/simple_os/arch/x86_32/` contains:
  - `boot/crt0.s`
  - `linker.ld`
  - `boot/baremetal_stubs.c`
- Current x86_32 app/wrapper depth is still thin compared with x86_64.

### Existing x86_64 lane

- `examples/simple_os/arch/x86_64/boot/crt0.s` performs a 32-bit Multiboot handoff and then enters long mode.
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` owns the freestanding runtime for the wrapper lane.
- `src/os/qemu_runner.spl` already maps `Architecture.X86_64` to:
  - `qemu-system-x86_64`
  - `-machine q35`
  - `-cpu qemu64`
- `examples/simple_os/arch/x86_64` is the rich wrapper lane for desktop, WM, browser, tools, and probes.

## Known Working vs Broken

### Known working enough

- x86_64 OS smoke/desktop-related boot paths are documented as reaching runtime markers in `doc/01_research/local/simpleos_qemu_validation.md`.
- x86_64 GUI/WM boot reaches framebuffer/input/compositor stages before later runtime issues.
- x86_64 tools and SSH lanes boot far enough to exercise real subsystems.
- x86_32 boot and console infrastructure exist and are structurally correct.

### Known broken

- Current x86_64 browser/desktop wrapper images do not produce a stable boot-to-marker result.
- Raw probe work showed the immediate failure is deeper than string formatting.
- The generated x86_64 wrapper `spl_start` still receives an absurd stack reservation in disassembly, which points at wrapper/codegen/runtime lowering rather than browser logic.
- The current x86_64 ELF32 wrapping path is a packaging workaround, not a clean long-term architecture.
- Current x86_32 app/browser wrapper coverage is not yet deep enough to serve as the full acceptance lane.

## Architectural Reading

The stable split is not "one x86 wrapper for everything."

The repo already wants two x86 lanes:

- x86_32:
  - conservative boot/probe lane
  - Multiboot1/BIOS-friendly
  - simplest place to validate boot contracts, serial probes, and minimal browser/software-render checks
- x86_64:
  - richer runtime lane
  - long-mode wrapper
  - desktop, browser, services, and higher-level integration checks

This matches the current code layout better than continuing to force x86_64 artifacts through an ELF32 wrapper and treating that as the primary architecture.

## File-Level Recommendations

1. Extend `examples/simple_os/arch/x86_32/` with minimal browser and desktop wrapper entries.
2. Keep `src/os/kernel/arch/x86_32/` as the kernel-grade 32-bit boot/runtime source of truth.
3. Keep `examples/simple_os/arch/x86_64/boot/` as the full wrapper/runtime path for the 64-bit lane.
4. Add explicit x86_32 browser/desktop targets in `src/os/qemu_runner.spl`.
5. Keep `qemu-system-i386/qemu32` and `qemu-system-x86_64/qemu64` as distinct acceptance environments.
6. Share browser/desktop app logic above the boot/runtime boundary only.

## Recommended Direction

Use a dual-lane plan:

- x86_32 becomes the clean boot/probe lane.
- x86_64 remains the full runtime/browser/desktop lane.
- Browser validation is staged:
  - first prove software-render/browser markers on x86_32
  - then fix the x86_64 wrapper/codegen/runtime issue
  - then restore full desktop/browser acceptance on x86_64
