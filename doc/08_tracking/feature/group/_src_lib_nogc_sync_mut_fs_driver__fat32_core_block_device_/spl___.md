# `src/lib/nogc_sync_mut/fs_driver/{fat32_core,block_device}.spl`_+

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0007"></a>FR-DRIVER-0007 | Port `Fat32Core` + `BlockDevice` into `src/lib/nogc_sync_mut/fs_driver/` to unblock FS adapter forwarding | `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl` + `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` `fat32_stub.spl` used to pull the real FAT32 driver via `use os.services.fat32.fat32.{Fat32Driver as Fat32Core, BlockDevice}`. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
