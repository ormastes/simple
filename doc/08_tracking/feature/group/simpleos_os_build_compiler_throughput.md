# simpleos-os_build/compiler_throughput

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SOS-023"></a>FR-SOS-023 | Reduce native-build timeout on x86_64 WM entry | The x86_64 full OS native-build path should not fail because the unrelated `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl` module exceeds the current per-file 60 second compilation timeout. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
