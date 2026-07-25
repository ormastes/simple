# simpleos-os_process_lifecycle

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SOS-021"></a>FR-SOS-021 | Add safe execve argv/envp copy-in helpers | Add reusable, validated user-memory helpers for `copyin_u64` and NUL-terminated argv/envp vector copy-in. Helpers must validate each pointer, enforce argument count and byte caps, detect termination, and safely read across user mappings bef | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-SOS-024"></a>FR-SOS-024 | Complete syscall 13 direct user-process handoff | Finish the direct syscall 13 app-launch path so a mounted app image can be built, mapped, registered as a scheduler-owned user task, enqueued from the syscall/trap path, and entered through the x86_64 user return path. The resident-manifest | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
