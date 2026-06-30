# `src/compiler/70.backend/linker/lib_smf.spl`_+_codegen

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0004"></a>FR-DRIVER-0004 | `.drv_manifest` SMF section + emission from `@driver` attribute | The runtime decoder already exists (`src/lib/nogc_sync_mut/driver/loader.spl::decode_manifest` reads the "DRVS"" magic + 64B header defined in `driver/manifest.spl`). The writer is missing: the compiler must emit an SMF section kind" | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
