<!-- codex-design -->
# Architecture: x86 Dual-Arch QEMU Boot

## Decision

Use a split-lane x86 design:

- `x86_32` is the boot/probe lane
- `x86_64` is the full runtime/browser/desktop lane

This preserves both architectures without forcing one boot/runtime model to masquerade as the other.

## Rationale

### Why not a unified wrapper

- The repo already separates x86_32 and x86_64 boot/runtime code.
- The current x86_64 wrapper path shows codegen/runtime instability at `spl_start`.
- A shared wrapper would blur ABI and boot-protocol boundaries at the exact point the system needs them to be explicit.

### Why x86_32 owns probe bring-up

- Multiboot1/BIOS expectations are naturally 32-bit-compatible.
- The repo already has a dedicated x86_32 kernel/console boot stack.
- A simpler lane is the right place for early deterministic probes.

### Why x86_64 owns full runtime

- The current desktop/browser/service runtime investment is already in the x86_64 wrapper lane.
- Long-mode transition, richer runtime stubs, and desktop/browser assets already live there.

## Layering

### Layer 1: Arch-specific boot/runtime

Owned by:

- `src/os/kernel/arch/x86_32/**`
- `examples/simple_os/arch/x86_32/**`
- `examples/simple_os/arch/x86_64/boot/**`
- `examples/simple_os/arch/x86_64/**`

Responsibilities:

- boot header and entry
- mode switch
- early serial
- baremetal runtime ABI
- debug-exit path

### Layer 2: QEMU lane binding

Owned by:

- `src/os/qemu_runner.spl`
- test harnesses under `test/qemu/os/common/**`

Responsibilities:

- target triple
- output artifact naming
- QEMU binary, machine, CPU
- lane naming and lane visibility

### Layer 3: Shared app/browser logic

Owned by:

- `src/lib/gc_async_mut/gpu/browser_engine/**`
- `src/lib/common/render_scene/**`
- `src/os/apps/**`

Responsibilities:

- DOM/layout/paint logic
- browser application behavior
- desktop/app logic above boot/runtime

## Architecture Rules

1. Boot/runtime code is architecture-specific.
2. Shared browser/desktop logic begins only after the boot/runtime boundary.
3. x86_32 and x86_64 QEMU tuples remain explicit and separate.
4. An ELF32-wrapped x86_64 artifact is compatibility/investigation output, not the architectural definition of native x86_64 support.

## Immediate Implementation Shape

### x86_32

- explicit probe target constructors
- minimal probe entrypoints
- later browser-soft smoke lane

### x86_64

- explicit wrapper investigation targets
- browser/desktop runtime targets kept visible
- wrapper/codegen repair remains separate work

## Risks

- ABI leakage between 32-bit and 64-bit runtimes
- false positives from cached spec runs
- continued use of compatibility packaging as if it proved native x86_64 support
