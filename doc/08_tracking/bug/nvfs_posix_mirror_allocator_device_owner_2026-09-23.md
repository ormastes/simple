# NVFS POSIX mirror allocator survives block-device replacement

Status: fix in progress; independent of the NVFS raw-sector fixture correction.

The POSIX mirror cursor was process-global. Every write advanced it by 32
sectors, while `nvfs_arena_set_block_device` replaced the process-local device
without changing that cursor. Six writes on a 256-sector device left the next
base at LBA 256. A replacement 256-sector device then received an out-of-range
request at data LBA 257. The append failure was ignored after the DBFS write.

The canonical `block_device_owner` now owns one fixed-size mirror cursor and
binds it to a stable device identity. Re-registering the active device retains
the cursor; a fresh identity starts at LBA 64. Retired identities cannot be
reactivated because their prior cursor is no longer retained. A monotonic
high-water mark makes this decision with constant-size state. Capacity is
checked before each 32-sector reservation, before any physical write. Unknown
identity or capacity fails the mirror write explicitly. The mirror writes
sectors directly using read-modify-write, preserving untouched trailing bytes
without adding an arena metadata entry or linear arena lookup per POSIX write.

The regression spec covers repeated writes, both 256-sector boundaries,
replacement, same-device re-registration, A→B→A rejection, zero physical
writes on capacity rejection, raw sector bytes, and old-device isolation.

The DBFS/shadow write commits before the mirror attempt. A mirror error is
returned to the caller even though DBFS bytes may already be visible. The
spec asserts this partial-commit behavior rather than claiming atomicity.

Structural performance/memory evidence: owner lookup and retirement decisions
are O(1), owner state is a fixed number of scalars plus one device slot, and
the mirror write reuses the prior per-sector read-modify-write pattern. Removing
the abandoned arena record also removes a growing metadata array and linear
arena-id scan from this path. Measured performance/memory evidence is absent.

Native/QEMU verification and measured write latency/peak RSS: TODO before
production acceptance. No performance result is claimed from the structural
check alone.
