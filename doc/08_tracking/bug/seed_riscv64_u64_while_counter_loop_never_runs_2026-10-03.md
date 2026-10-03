# Seed riscv64 freestanding: `u64` while-counter loop body never runs (2026-10-03)

**Status:** open (worked around). **Target:** `riscv64gc-unknown-none-elf`,
seed cranelift backend, built from release/1.0 `d4bfccb7bc9`.

## Observed

In `examples/09_embedded/simple_os/arch/riscv64/nvfs_root_entry.spl` (first
draft), this loop never executed its body under QEMU, although
`rv64_virtio_mmio_blk_slot_count()` returned 8 and
`rv64_virtio_mmio_blk_slot_is_block(7u64)` returned true when called directly:

```simple
var slot: u64 = 0u64
while slot < rv64_virtio_mmio_blk_slot_count():   # fn returning u64 (8)
    if rv64_virtio_mmio_blk_slot_is_block(slot):
        ...
    slot = slot + 1u64
```

Rewriting the counter as `var slot: i64 = 0` with
`while slot < rv64_virtio_mmio_blk_slot_count().to_i64():` and passing
`slot.to_u64()` made the loop run correctly (current committed form).

## Not yet isolated

Whether the fault is the unsigned `<` against a call result, the `u64` local's
initial value, or the `u64` `+` is unknown; a minimal native-build repro on
riscv64 and x86_64 freestanding is the next step. The i64 workaround is in
`nvfs_root_entry.spl::find_nvfs_slot`.
