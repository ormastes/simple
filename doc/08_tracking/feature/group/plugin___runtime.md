# plugin_/_runtime

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-PLUG-0001"></a>FR-PLUG-0001 | WFFI f64 calling-convention extern | Add `extern fn spl_wffi_call_f64(fptr: i64, args: [f64], nargs: i64) -> f64` alongside the existing i64 variant. Today WFFI is i64-only; AC-3b's `rt_gemm_add(double*, double*, double*, i64, i64, i64) -> void` works through pointer args beca | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | [doc/02_requirements/feature/runtime_api_block_sugar_plugins.md](../../../02_requirements/feature/runtime_api_block_sugar_plugins.md#feature-FR-PLUG-0001) |
