# engine2d

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-ENGINE2D_TRAIT_FACADE_BACKEND_EXECUTION_2026_06_02"></a>ENGINE2D_TRAIT_FACADE_BACKEND_EXECUTION_2026_06_02 | Engine2D Facade Must Preserve Backend Pixel Mutations | Date: 2026-06-02 Status: open Area: Engine2D, render backends, web renderer parity ## Problem Backend-executed parity evidence found that direct concrete backends preserve drawn pixels, but the generic `Engine2D` facade path can lose pixel  | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
