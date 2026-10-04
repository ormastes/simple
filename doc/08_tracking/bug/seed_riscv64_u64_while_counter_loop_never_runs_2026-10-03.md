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

## Related evidence (2026-10-04): ordering compare on a method result goes dynamic

`src/os/kernel/boot/fdt_blob.spl` `FdtBlob.valid()` first read
`if self.be32(4u64) > self.size:` (`be32` declared `-> u64`). The riscv64
seed lowered exactly the four ordering compares whose operand was a
`self.be32(..)` call result to the DYNAMIC `rt_native_cmp`, which treats a raw
integer with low tag bits `001` as a heap pointer: the guest took a load
access fault (`scause=5 stval=0x10`) inside `rt_native_cmp` on the first boot.
Found by scanning the kernel's cranelift literal pools for `rt_native_cmp`'s
address; no other function in the new modules referenced it. Binding each call
result to a typed local (`val total: u64 = self.be32(4u64)`) first made the
compares native. This is likely the same root cause as the loop above: the
seed loses the declared return type of some call results in ordering compares
and falls back to dynamic comparison.

## Not yet isolated

Whether the fault is the unsigned `<` against a call result, the `u64` local's
initial value, or the `u64` `+` is unknown; a minimal native-build repro on
riscv64 and x86_64 freestanding is the next step. The i64 workaround is in
`nvfs_root_entry.spl::find_nvfs_slot`.
