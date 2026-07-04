# `src/lib/nogc_sync_mut/fs_driver/driver_adapter.spl`_+_`gpu_driver/driver_adapter.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0006"></a>FR-DRIVER-0006 | Real `fs_driver` + `gpu_driver` adapter integration | FS adapter probe/attach path verified 2026-05-29. The Phase D adapters register the drivers but stub every op (`init → Ok(())`, `probe → Reject`, everything else either `Ok(())` or `NotSupported`). Replace these stubs with real | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
