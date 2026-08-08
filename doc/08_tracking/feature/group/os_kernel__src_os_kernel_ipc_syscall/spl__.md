# os-kernel_(src/os/kernel/ipc/syscall.spl_+

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SPM-0002"></a>FR-SPM-0002 | Caller-TaskId → privilege-mirror lookup for `sys_priv_check` (case 110) | src/os/kernel/privilege/privilege_bridge.spl) `_handle_spm_priv_check` in syscall.spl currently always returns `0` (deny) because it has no path from "the syscall that just arrived"" to `bridge_lookup(caller_task_id)`. Wire the caller's `Tas" | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
