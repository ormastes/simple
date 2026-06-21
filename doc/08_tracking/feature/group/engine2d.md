# engine2d

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-ENGINE2D_TRAIT_FACADE_BACKEND_EXECUTION_2026_06_02"></a>ENGINE2D_TRAIT_FACADE_BACKEND_EXECUTION_2026_06_02 | Engine2D Facade Must Preserve Backend Pixel Mutations | Date: 2026-06-02 Status: current Area: Engine2D, render backends, web renderer parity. Software and cpu_simd facade pixel mutation evidence is covered and the web parity harness now routes reduced-scene software/cpu_simd through Engine2D; macOS Metal proof remains open. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | doc/06_spec/test/01_unit/gpu/engine2d_trait_facade_backend_spec.md; doc/06_spec/test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.md |
