# RV64 Boot DTB Capability V1

The RISC-V boot handoff owns the only mutable topology/cache-discovery state.
Firmware lends the physical DTB pointer only for the duration of
`riscv_noalloc_dtb_capability_init`; no address, slice, text, or decoded dynamic
object escapes that call.

The owner performs one bounded structure walk after observing `a0`/`a1` and
before publishing handoff readiness, PMM, or heap state. It validates the FDT
header/version/compatibility, physical-address arithmetic, 2 MiB size ceiling,
non-overlapping structure/string ranges, the complete reservation list through
its zero/zero terminator, tokens, root closure, nesting depth, required CPU
parent address/size cell declarations, duplicate relevant properties, enabled
CPU `reg` values, uniqueness, and the
32-hart capacity. The observed boot hart is always committed as logical CPU 0.

Committed state is one `[u64; 32]`, a count, a validity bit, the enabled-CPU
intersection of exact `zicbom` ISA tokens, and one consistent nonzero
power-of-two `riscv,cbom-block-size`. Failure atomically falls back to the
observed boot hart, Zicbom disabled, and a 64-byte stride.

`hal_smp` consumes logical-to-firmware-hart mapping in O(1). SBI HSM receives
the physical hart ID, and IPI delivery derives the correct 64-hart mask window
and mask base even for sparse IDs above 63. Broadcast groups targets into one
dispatch per occupied 64-hart window without allocation; sparse legacy windows
use the existing absolute CLINT fallback. Pending-vector and boot-arg
slots remain logical indices. The existing eight-slot live-SMP storage remains
an honest blocker for starting logical CPUs 8..31; discovery does not claim
those storage paths are ready. `hal_cache` consumes the immutable capability
snapshot in O(1), eliminating production ISA-text probing and the synthetic
64-byte authority.

Time is O(D + 64P + C²), where D is the single bounded structure walk, P is the
number of properties, and C <= 32 is enabled CPUs. Broadcast grouping is also
bounded O(C²). Each strings-table property
name lookup is capped at 64 bytes rather than scanning the whole strings block;
the C² uniqueness check has a strict 1,024-comparison
ceiling and avoids a heap hash table. Persistent storage is 256 bytes plus
scalars. Parsing allocates nothing and retains no firmware payload.
