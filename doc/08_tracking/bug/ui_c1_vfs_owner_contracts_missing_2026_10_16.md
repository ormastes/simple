# UI C1 VFS missing owner contracts

2026-10-16. Source repair prepared; native validation UNRUN.

Direct FAT32 reader now requests allocation through nvme_boot_runtime_alloc_dma(size:u64)->Result<DmaAddrs,text> on the sole g_nvme owner. Both reads use the existing namespace1/SYSTEMqueue owner read function. The original allocation size4096, descriptor allocation_id2, scalar fields, error branches and synchronous sequence are unchanged. Existing _shared_dma constructs allocation_id1 and is intentionally not substituted. No new parallel-safety claim.

Q35 performance code uses existing initialized/provider/pure-Simple getters. The state owner's mounted-root read-once helper preserves nil=>empty and the same root driver/path read; it does not substitute the separate pure-NVMe root. Existing pure byte/ELF/MMIO/interface helpers are imported explicitly within the same capsule without exporting or copying mutable globals. Byte-to-text count arguments match the provider's i64 contract.

The state module imports public g_vfs_read_file_bytes from vfs_init to retain full original dispatch. Graph: vfs_init -> vfs_boot_init -> vfs_boot_state -> vfs_init. Compiler import resolver contains cycle/re-entry memo; this exact signature/import path remains subject to final genuine native qualification. No dispatch duplication or partial reader fallback.
