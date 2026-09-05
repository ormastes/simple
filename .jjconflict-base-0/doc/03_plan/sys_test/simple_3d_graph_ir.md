<!-- codex-design -->
# Simple 3D Graph IR Test Plan

## Coverage

| Requirement | Evidence |
|-------------|----------|
| REQ-3D-GRAPH-001 | Unit spec records a pass and two draws, then checks pass/draw/resource counts. |
| REQ-3D-GRAPH-002 | Unit spec verifies pass-local pipeline/texture/mesh sorting and pass-boundary preservation. |
| REQ-3D-GRAPH-003 | Unit spec replays an optimized graph through `SoftwareRenderBackend3D`. |
| 3D hardening | Existing Math3D spec covers `Vec3`, `Mat4`, `Quaternion`, and `Transform3D` methods used by the software 3D renderer. |

## Commands

```sh
SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/engine/render/graph_ir3d.spl
SIMPLE_LIB=src bin/simple check src/lib/common/engine/math3d.spl
SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/engine/render/software_backend3d.spl
SIMPLE_LIB=src bin/simple check test/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/lib/engine/math3d_spec.spl --mode=interpreter
```
