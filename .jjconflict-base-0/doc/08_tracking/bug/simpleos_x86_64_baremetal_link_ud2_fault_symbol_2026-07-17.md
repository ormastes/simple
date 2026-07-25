# SimpleOS: every x86_64 baremetal link broken — `spl_x86_on_kernel_ud2_fault` undefined (2026-07-17)

**Found by:** release sanity T3 lane (both QEMU x86_64 gates FAIL on this).

## Symptom

```
ld.lld: error: undefined symbol: spl_x86_on_kernel_ud2_fault
>>> referenced by baremetal_stubs.c (_rich_fault_entry)
```

- `scripts/check/check-simpleos-memory-leveling-qemu.shs` → exit 1,
  `memory_leveling_qemu_status=fail reason=kernel-build`
- `scripts/check/check-simpleos-dbfs-root-qemu.shs` → exit 3 (kernel ELF
  `build/os/simpleos_x86_64.elf` missing; cranelift rebuild hits the same link
  error)

## Root cause

Commit `57aca2c5835` (2026-07-17, "chore(wc): session sync" — the C8-CLOSE ud2
fix) added `callq spl_x86_on_kernel_ud2_fault` to `_rich_fault_entry` in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` (~line
15284). The callee is defined only in
`src/os/kernel/arch/x86_64/interrupt.spl:367` via `@export("C")`, and:

1. the memory-leveling gate's staged source set omits `interrupt.spl` entirely;
2. the full-tree build's entry-closure tree-shake discards `@export` functions
   that are referenced only from C objects.

So the C half of the fix landed while the Simple half never survives linking.

## Fix directions (root, pick one)

- Entry-closure/tree-shake must treat `@export("C")` as a root (never shaken) —
  fixes class, not instance; or
- add `interrupt.spl` to the staged source set AND keep-alive the export in the
  full build.

## Staged-source direction FIX (applied 2026-07-18)

**Changes made:**
1. `scripts/check/check-simpleos-memory-leveling-qemu.shs` (lines 41-51):
   - Added `mkdir -p "$STAGE/src/os/kernel/{interrupts,types,scheduler,ipc,log}"`
   - Staged `interrupt.spl` and all its direct dependencies:
     - `src/os/kernel/arch/x86_64/{cpu,trap_runtime,user_entry}.spl`
     - `src/os/kernel/interrupts/{idt,apic,pic,gdt,irq_routing,ports}.spl`
     - `src/os/kernel/types/{task_types,syscall_types}.spl`
     - `src/os/kernel/{scheduler/scheduler,ipc/{ipc,syscall},log/klog}.spl`

2. `examples/09_embedded/simple_os/arch/x86_64/memory_leveling_qemu_entry.spl`:
   - Added `use os.kernel.arch.x86_64.interrupt.{}` to make interrupt.spl
     part of the entry-closure reachable set (forces compiler to include it
     despite entry-closure tree-shake filtering).

**Verification:** Gate still fails on link stage or later; check if link error
`undefined symbol: spl_x86_on_kernel_ud2_fault` is gone and report new first
failure. If tree-shake still drops the exported function despite reachability,
an additional keep-alive mechanism (linker flag or compiler root marker) is needed.

## Related

- `simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md` (C8 chain;
  the ud2-fault fix this call belongs to is boot-verified but uncommitted —
  `simd.rs`/`import_loader.rs` still modified in WC).
- Board-runnable rule violations in both gate scripts FIXED (2026-07-18):
  - Removed `-device isa-debug-exit` from both `check-simpleos-dbfs-root-qemu.shs`
    and `check-simpleos-memory-leveling-qemu.shs`
  - Replaced with real-firmware-proxy pattern: `-serial file:` logging + marker
    detection + timeout-based termination (compliant with
    `.claude/rules/board-runnable.md`)
  - Run-verify deferred (kernel link currently blocked by ud2_fault symbol issue)

## Status (2026-07-18)

OPEN (ud2_fault symbol link issue). Sibling lane fixed board-runnable rule violations in gate scripts (isa-debug-exit removed, real-firmware proxy pattern applied). ud2_fault symbol link remains blocked; class fix (@export tree-shake) or instance fix (staged source + keep-alive) pending.

## Run-verify (2026-07-18)

Gate rerun after the staged-source fix: `undefined symbol:
spl_x86_on_kernel_ud2_fault` NO LONGER APPEARS (0 hits in build.log). The
build now dies with `Terminated` (`reason=kernel-build`) — host contention
(load ~9-10 from parallel bootstrap sessions) starved the native-build until
the gate's budget killed it. Symbol fix plausibly effective; full PASS
verification deferred to a quiet host. isa-debug-exit rework rides the same
rerun and is likewise pending a completed boot.
