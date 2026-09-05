# Stage3 Freestanding Struct-by-Value Corrupts PMM

**Status (2026-07-17):** Likely fixed by commits `ca1e18c1744a` and `7c30ce49d04f` per triage evidence (see note below).

The stage3 Cranelift x86_64 freestanding build passed `PhysMemManager` by value
to `_bitmap_clear`. The callee read a corrupted `bitmap_addr` and repeatedly
wrote to address `-122`, producing recovered page faults instead of initializing
the PMM bitmap.

The PMM hot path now passes the scalar bitmap address across helper boundaries;
compatibility wrappers remain for existing callers. The compiler needs an ABI
regression covering a four-field `u64` struct passed by value between modules
and must either lower it correctly or reject the build.

A later production run proved the corruption also occurs when the aggregate is
an unused parameter: `vmm_init(pmm_get_manager(), 0)` entered VMM but failed in
its first `_alloc_table_page`, even though `vmm_init` never reads the manager.
The production desktop now calls scalar-only
`vmm_init_from_global_pmm(hhdm_offset)`. The compatibility API delegates to the
same body for callers built with a correct aggregate ABI.

The defect also affects enum payloads. Stage3 lowered `pmm_alloc_page()` as a
`PageFrame?` that passed `rt_is_some`, while `rt_enum_payload` returned zero;
VMM then trapped on the nil `PageFrame` payload. `pmm_alloc_page_raw()` now
owns scalar bitmap allocation directly, and VMM table allocation consumes that
raw physical address. This removed a 578 KB repeated-fault serial storm.

Direct QEMU boot also cannot safely parse module-global Limine request structs
and optional response payloads under this ABI. The direct production desktop
therefore uses `arch_x86_64_direct_boot_init()`, which retains fault-hook,
per-CPU, CPUID-topology, and syscall initialization without pretending the
multiboot wrapper supplied Limine aggregates.

## Triage note (2026-07-17)

Commits `ca1e18c1744a` and `7c30ce49d04f` likely address the aggregate ABI and enum-payload defects described above. The workarounds (scalar-only APIs, direct-boot path) are confirmed in production use. Pending runtime verification: fresh stage3 freestanding build must compile and boot with zero PMM/VMM faults.
