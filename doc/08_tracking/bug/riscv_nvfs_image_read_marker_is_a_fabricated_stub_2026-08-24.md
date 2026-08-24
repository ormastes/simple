# `[riscv-nvfs] image read ok` is a fabricated stub, not nvfs evidence (2026-08-24)

- Status: OPEN (P2)
- Measured in `/mnt/data/worktrees/goal-lane-d-simpleos-fs`

## Why this matters

A real riscv64 guest boot prints, in order:

```
SimpleOS RV64 boot OK
[riscv-nvfs] image read ok
FS_MOUNT_OK
```

Read naively that says nvfs was read and then mounted. It says no such thing,
and it has already been cited as nvfs evidence in
`doc/08_tracking/bug/simpleos_guest_simple_cli_staged_but_never_executed_2026-08-24.md`.

## What is actually true

The marker is emitted at `examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl:32`
(and the riscv32 / shared-service / desktop-service siblings) guarded by

```
extern fn rt_riscv_nvfs_probe() -> i64
```

`rt_riscv_nvfs_probe` **has no implementation anywhere in `src/` or `scripts/`**.
It is listed as a fabricated stub in `config/simpleos_fabricated_rt_baseline.sdn:220`
(`simpleos_riscv64_smf_fs.elf rt_riscv_nvfs_probe`), i.e. the linker auto-stubs it,
and `test/01_unit/compiler/backend/rv64_real_runtime_link_contract_spec.spl:10`
exists specifically to assert the linker must not emit
`rt_riscv_nvfs_probe(void){return 1;}`.

So the marker prints because a stub returned a truthy constant. Nothing read an
nvfs image; no nvfs image is even produced for that lane. The `FS_MOUNT_OK` that
follows is the **FAT32** mount — confirmed by the same boot going on to
`ELF_LOAD_OK` and `FS_LS_*` over 8.3 FAT names.

## Fix order

1. Either implement `rt_riscv_nvfs_probe` against a real nvfs image, or delete
   the marker. A serial marker that a fabricated stub can print is worse than no
   marker: it manufactures evidence for a filesystem that is not there.
2. Re-audit the other markers in `config/simpleos_fabricated_rt_baseline.sdn`
   for the same defect class — any fabricated `rt_*` that gates a printed
   acceptance marker is a false-evidence source.
