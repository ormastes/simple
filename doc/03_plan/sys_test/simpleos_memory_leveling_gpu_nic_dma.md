# SimpleOS GPU/NIC/DMA Memory Leveling System Test Plan

## Scope

The executable SPipe spec covers REQ-001 through REQ-015 with interpreter,
native, and capability-gated QEMU evidence.

## Scenarios

1. Independently construct and mutate the language and SimpleOS configurations;
   prove no shared mutable state or field leakage.
2. Preserve allocation identity through legal CPU/device transitions and reject
   every out-of-order, wrong-owner, wrong-direction, and released operation.
3. Balance nested pins and in-flight work; reject underflow, duplicate completion,
   release, migration, and swap while protected.
4. Allocate a proven contiguous run and an explicit segment list; inject partial
   failure and prove all pages are released.
5. Inject VMM map/unmap failures and prove mappings, page references, and bytes
   remain unchanged after rollback.
6. Write deterministic byte patterns to swap, restore and compare every byte,
   then cover disabled/full/I/O/checksum/missing-slot failures.
7. Apply normal through emergency pressure and prove reservations, watermarks,
   cooldown, and the 64-candidate hard bound.
8. Prove stats snapshots use maintained counters and match all lifecycle events.
9. Exercise canonical DMA direction/map/sync/unmap and reject unsupported
   non-coherent cache maintenance.
10. Exercise virtio GPU backing segments and busy detach protection.
11. Exercise virtio NIC RX/TX synchronization, descriptor chains, completion,
    and queue reset draining.
12. Run separate language placement and SimpleOS kernel evidence so either config
    can evolve without importing the other.
13. Run native PMM/VMM/swap integration and QEMU x86 virtio/swap evidence while
    asserting unsupported physical migration claims remain unavailable.

## Acceptance

Every requirement has at least one non-placeholder assertion. Generated manual
steps must describe setup, action, and observable result. No executable `.spl`
file is placed under `doc/06_spec`.
