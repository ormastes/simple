# driver_/_compiler_frontend_+_hir_lowering

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0001"></a>FR-DRIVER-0001 | Compiler sugar for `@driver(...)` and `@native_lib(...)` attributes | Today every driver registers into the shared registry by calling `register_static_driver(manifest, ops)` from a hand-written registration fn. The design doc promises the one-liner syntax `@driver(class = DriverClass.Block, vendor = 0x8086,  | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
