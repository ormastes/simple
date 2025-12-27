## Part 17: Testing Strategy

### 17.1 Unit Tests

```simple
# Test math primitives
fn test_vector_operations()
fn test_matrix_multiplication()
fn test_quaternion_rotations()
fn test_transform_composition()

# Test scene graph
fn test_scene_hierarchy()
fn test_component_system()
fn test_world_transform_computation()
```

### 17.2 Integration Tests

```simple
# Test rendering pipeline
fn test_render_empty_scene()
fn test_render_single_mesh()
fn test_render_with_lights()
fn test_render_with_shadows()
fn test_render_transparent_objects()
```

### 17.3 Visual Regression Tests

- Capture reference images
- Compare rendered output
- Detect visual regressions
- Generate diff images

---


## Part 18: Documentation Requirements

Each public API must include:

- **Purpose**: What the type/function does
- **Parameters**: Description of each parameter
- **Returns**: What is returned
- **Examples**: Code example showing usage
- **Notes**: Performance considerations, limitations

Example:

```simple
# Create a perspective camera
#
# Parameters:
#   fov_y: Vertical field of view in radians
#   aspect: Aspect ratio (width / height)
#   near: Near clipping plane distance
#   far: Far clipping plane distance
#
# Returns:
#   Camera configured with perspective projection
#
# Example:
#   let camera = Camera::perspective(90.0_deg.to_rad(), 16.0/9.0, 0.1, 100.0)
#
# Notes:
#   - Uses Vulkan convention (Y-down clip space, Z [0, 1])
#   - Near plane must be > 0
#   - Far plane must be > near plane
#
pub fn perspective(fov_y: Radians, aspect: f32, near: f32, far: f32) -> Camera
```

---


## Part 19: Compatibility Matrix

| Feature | Vulkan | CUDA | Software | Notes |
|---------|--------|------|----------|-------|
| Basic rendering | ✅ | ❌ | ✅ | CUDA is compute-only |
| PBR shading | ✅ | ❌ | ✅ | |
| Shadow mapping | ✅ | ❌ | ⚠️ | Slow on CPU |
| Post-processing | ✅ | ❌ | ✅ | |
| Compute shaders | ✅ | ✅ | ✅ | Particle systems, etc. |
| Ray tracing | ⚠️ | ❌ | ❌ | Vulkan 1.2+ with RT extension |

---


## Part 20: Glossary

- **PBR**: Physically-Based Rendering
- **IBL**: Image-Based Lighting
- **CSM**: Cascaded Shadow Maps
- **MSAA**: Multi-Sample Anti-Aliasing
- **FXAA**: Fast Approximate Anti-Aliasing
- **LOD**: Level of Detail
- **AABB**: Axis-Aligned Bounding Box
- **ECS**: Entity-Component-System
- **FPS**: First-Person Shooter (camera controller)
- **glTF**: GL Transmission Format (3D asset format)

---


## Appendix A: Coordinate System Conversion

When importing assets from other engines:

| Engine | Coord System | Conversion to Simple |
|--------|--------------|---------------------|
| Unity | Y-up, left-handed | Negate Z |
| Unreal | Z-up, left-handed | Swap Y/Z, negate new Z |
| Blender | Z-up, right-handed | Swap Y/Z |
| Maya | Y-up, right-handed | None (matches Simple) |

---

## Appendix B: Material Property Ranges

| Property | Range | Default | Physical Meaning |
|----------|-------|---------|------------------|
| Albedo | [0, 1] | 0.5 | Surface color reflectance |
| Metallic | [0, 1] | 0.0 | 0 = dielectric, 1 = metal |
| Roughness | [0, 1] | 0.5 | Surface microsurface roughness |
| AO | [0, 1] | 1.0 | Ambient occlusion factor |
| Emissive | [0, ∞) | 0.0 | Emitted light in nits |
| Normal Scale | [0, 2] | 1.0 | Normal map strength |

---

**End of Specification**
