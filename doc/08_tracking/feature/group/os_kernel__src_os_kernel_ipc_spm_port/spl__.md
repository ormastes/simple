# os-kernel_(src/os/kernel/ipc/spm_port.spl_+

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SPM-0003"></a>FR-SPM-0003 | Rebind syscall for SPM port when real SPM task id is known | src/os/kernel/ipc/syscall.spl + src/os/kernel/types/syscall_types.spl) Kernel init now registers `SPM_WELL_KNOWN_TASK_ID = 0xfffffff0` via `spm_port_register` (see `init_services.spl::init_spm_port` and the `6353c53526` commit body). When t | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
