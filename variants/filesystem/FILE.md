# Filesystem variation slots

Planned filesystem provider slots include FAT32, NVFS and DBFS, independently
of the sibling [OS](../os/FILE.md) group. Multiple OS providers can reuse one
filesystem implementation, and one OS can mount multiple filesystem providers.
Keep implementation source with its existing owner; do not duplicate it per OS.

Applications use SOSIX filesystem operations. Composition binds an admitted
filesystem provider per mount/resource to a compatible OS transport. Hosted
OS-managed filesystems need not expose their underlying disk format. Unsupported
operations fail explicitly; changing a default does not rebind open handles.

This folder documents planned selection seams, not implemented resolver support
or a verified OS/filesystem matrix. SOSIX statfs and truncate routing remains open.
See the [selected design](../../doc/05_design/compiler/perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-selected-os-and-filesystem-separation)
and [existing implementation plan](../../doc/03_plan/compiler/perf/runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md#2026-10-11-os-and-filesystem-variation-refinement).
