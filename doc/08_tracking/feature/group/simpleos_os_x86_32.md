# simpleos-os_x86_32

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SOS-025"></a>FR-SOS-025 | Bring x86_32 from boot-probe target to full OS parity | Treat x86_32 as a documented boot/probe target until it has the same observable OS surface as the x86_64 lane. Do not mark x86_32 as a full OS target until it can boot, enter protected/user execution paths, run the syscall/process/shell/sto | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
