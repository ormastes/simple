# Native AArch64 i32 array negative value zero-extension

## Status

Open compiler defect; Simple Web child-link storage now uses its canonical i64
index width and no longer triggers the defect.

## Evidence

In the strict SimpleOS ARM64 QEMU ELF, `[-1; node_count]` correctly stored
`0xffffffffffffffff`. The generated load in `build_selector_context` then used
`and x23, x8, #0xffffffff`, producing `4294967295` instead of sign-extending the
i32 value. The `child >= 0` loop indexed out of bounds, decoded NIL as `3`, and
spun forever. A live QEMU gdb backtrace repeatedly stopped in that loop.

## Required compiler regression

Native-build an AArch64 entry that stores `-1` in `[i32]`, loads it, and checks
`value < 0`. The emitted code must sign-extend the loaded i32 (`sxtw` or an
equivalent signed operation), and the executable must take the negative branch.
Changing one consumer to i64 is not proof that the compiler defect is fixed.
