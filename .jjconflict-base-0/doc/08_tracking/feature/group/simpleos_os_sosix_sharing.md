# simpleos-os_sosix_sharing

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SOS-022"></a>FR-SOS-022 | Populate dataset_create_from_file from VFS bytes | Change `dataset_create_from_file(fd, offset, len, flags)` from an ABI-shaped sealed-handle stub into a real immutable byte snapshot populated from the VFS or open-file-description layer. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
