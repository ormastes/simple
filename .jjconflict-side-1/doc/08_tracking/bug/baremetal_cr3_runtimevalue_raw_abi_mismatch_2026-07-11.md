# Baremetal CR3 RuntimeValue/Raw ABI Mismatch

**Status:** Resolved — workaround deployed; live QEMU evidence confirms correct CR3 and boot progression.

The x86_64 baremetal stubs exposed `rt_write_cr3(RuntimeValue)` and decoded its
argument by shifting right three bits. Pure-Simple Cranelift extern calls pass
the declared `u64` physical address raw, so VMM attempted to load
`0x02800800` instead of the valid aligned root `0x14004000`, causing a silent
triple fault.

Legacy tagged helpers remain unchanged. The baremetal runtime now also exports
`rt_read_cr3_raw()` and `rt_write_cr3_raw(uint64_t)`, and the pure-Simple VMM
uses those explicit scalar primitives. Live QEMU evidence confirms CR3 becomes
`0x14004000` and execution reaches VFS, dynamic BGA scanout, Engine2D,
keyboard, mouse, compositor, and desktop shell initialization.
