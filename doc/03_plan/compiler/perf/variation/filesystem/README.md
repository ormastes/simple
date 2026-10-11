# Filesystem variation plan index

Filesystem axis: FAT32, NVFS, DBFS and compatible hosted filesystem providers.
Its sibling [OS axis](../os/README.md) owns native adapters. Select available
implementations separately from per-mount runtime instances; one OS can use
several filesystems, and several OS providers can reuse one filesystem owner.
Application filesystem operations use SOSIX.

Work, status and exit evidence stay in the [existing Item 5 plan](../../runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md#2026-10-11-os-and-filesystem-variation-refinement),
with the [selected design](../../../../../05_design/compiler/perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-selected-os-and-filesystem-separation)
and [acceptance rows I5-V09/V10](../../../../sys_test/item5_provider_size_acceptance_2026-10-02.md#independent-osfilesystem-acceptance--2026-10-11).
SOSIX statfs/truncate routing and live combination qualification remain open.
