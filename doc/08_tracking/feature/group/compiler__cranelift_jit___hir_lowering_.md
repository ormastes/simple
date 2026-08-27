# compiler_(cranelift_jit_/_hir_lowering)

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-012"></a>FR-COMPILER-012 | JIT-compile pure-Simple software rendering loops (unblock high-DPI 2D) | Pure-Simple per-pixel rasterizers (e.g. the SDF software renderer in `examples/06_io/ui/engine2d_shapes_gui.spl`) currently fall back to the tree-walk interpreter because JIT/HIR lowering bails with `Cannot infer type: TypedInteger(0, U32)` | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
