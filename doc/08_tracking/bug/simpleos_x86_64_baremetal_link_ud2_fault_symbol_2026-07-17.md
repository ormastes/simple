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

## Related

- `simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md` (C8 chain;
  the ud2-fault fix this call belongs to is boot-verified but uncommitted —
  `simd.rs`/`import_loader.rs` still modified in WC).
- Board-runnable rule violation confirmed while here: both gate scripts use
  `-device isa-debug-exit` (`check-simpleos-dbfs-root-qemu.shs:92`,
  `check-simpleos-memory-leveling-qemu.shs:81`), forbidden by
  `.claude/rules/board-runnable.md` (real-firmware proxy bar).
