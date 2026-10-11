# OS variation slots

Planned OS service adapter slots for Windows, Linux, BSD (including FreeBSD),
and SimpleOS. They are independent of the sibling [filesystem](../filesystem/FILE.md)
group. Actual native adapters stay in their existing layer-owned source paths.

OS adapters provide native transport, handles, waiting and resource lifecycle
under the common SOSIX contract. They do not contain copies of FAT32, NVFS or
DBFS. Existing `platform` overlays/configuration remain supported until the
resolver migration is implemented and verified.

No executable overlay or OS support is registered by this document. Follow the
[selected design](../../doc/05_design/compiler/perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-selected-os-and-filesystem-separation)
and [existing implementation plan](../../doc/03_plan/compiler/perf/runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md#2026-10-11-os-and-filesystem-variation-refinement).
