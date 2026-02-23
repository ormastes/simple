# 3D Engine Core Implementation Plan

**Date:** 2025-12-27
**Target:** Complete core 3D rendering engine
**Priority:** High
**Based on:** doc/spec/graphics_3d.md

---

## Overview

This plan details the implementation of the core 3D graphics engine for Simple language. The implementation is divided into phases, with each phase building on the previous one.

## Current State Analysis

### ✅ Already Implemented
- **Unified math module** (`rust/lib/std/src/math/`): Vec2/3/4, Mat3/4, Quat, Transform, Color in f32+f64 variants (column-major, GPU-ready)
- Scene graph structure (SceneNode trait in `game_engine/scene_node.spl`)
- Component system (Component trait, ComponentManager in `game_engine/component.spl`)
- Transform struct (`math.Transform` / `math.Transformd`)
- Vulkan backend infrastructure

**Note (2026-02-01):** Graphics math replaced by shared `math` module. Scene/render/shader work remains.

### ⚠️ Partially Implemented
- Quaternion (referenced but may be incomplete)
- Materials (referenced in examples but not implemented)
- Meshes (basic structure, missing implementation)
- Lights (structure exists, rendering not implemented)
- Loaders (mentioned but not implemented)

### ❌ Not Implemented
- Complete mesh primitive generation
- Material system (PBR, Phong, Unlit)
- Texture loading and management
- Shader compilation and management
- Shadow mapping
- Frustum culling
- Draw call batching
- Resource manager
- Asset loaders (OBJ, glTF, textures)
- Post-processing effects

---

## Phase 1: Foundation (Priority: Critical)

**Goal:** Complete foundational math and utility types

### Task 1.1: Complete Quaternion Implementation
**File:** `simple/std_lib/src/graphics/math/quaternion.spl`
**Depends on:** None
**Estimated Lines:** 250

```simple
pub struct Quaternion:
    x: f32
    y: f32
    z: f32
    w: f32

impl Quaternion:
    # Constructors
    fn identity() -> Quaternion
    fn new(x: f32, y: f32, z: f32, w: f32) -> Quaternion
    fn from_axis_angle(axis: Vec3, angle: f32) -> Quaternion
    fn from_euler(pitch: f32, yaw: f32, roll: f32) -> Quaternion
    fn from_rotation_matrix(mat: Mat3) -> Quaternion

    # Operations
    fn length(self) -> f32
    fn normalize(self) -> Quaternion
    fn conjugate(self) -> Quaternion
    fn inverse(self) -> Quaternion
    fn dot(self, other: Quaternion) -> f32
    fn slerp(self, other: Quaternion, t: f32) -> Quaternion
    fn to_matrix(self) -> Mat4
    fn to_euler(self) -> (f32, f32, f32)

    # Operators
    fn mul(self, other: Quaternion) -> Quaternion  # Quaternion multiplication
```

### Task 1.2: Complete Transform Implementation
**File:** `simple/std_lib/src/graphics/math/transform.spl`
**Depends on:** Task 1.1
**Estimated Lines:** 180

```simple
pub struct Transform:
    position: Vec3
    rotation: Quaternion
    scale: Vec3

impl Transform:
    # Complete all methods from spec
    fn identity() -> Transform
    fn to_matrix(self) -> Mat4
    fn inverse(self) -> Transform
    fn compose(parent: Transform, child: Transform) -> Transform
    fn look_at(self, target: Vec3, up: Vec3) -> Transform
    fn forward(self) -> Vec3
    fn right(self) -> Vec3
    fn up(self) -> Vec3
```

### Task 1.3: Complete Math Module Exports
**File:** `simple/std_lib/src/graphics/math/__init__.spl`
**Depends on:** Tasks 1.1, 1.2
**Estimated Lines:** 20

```simple
mod math

export use vector.*
export use matrix.*
export use quaternion.*
export use transform.*
```

### Task 1.4: Add Graphics Unit Types
**File:** `simple/std_lib/src/units/graphics.spl`
**Depends on:** None
**Estimated Lines:** 100

```simple
# Angle units
pub struct Degrees:
    value: f32

pub struct Radians:
    value: f32

impl Degrees:
    pub fn to_rad(self) -> Radians
    pub fn to_f32(self) -> f32

impl Radians:
    pub fn to_deg(self) -> Degrees
    pub fn to_f32(self) -> f32

# Literal syntax: 90.0_deg, 1.57_rad
```

### Task 1.5: Color Type
**File:** `simple/std_lib/src/graphics/math/color.spl`
**Depends on:** None
**Estimated Lines:** 150

```simple
pub struct Color:
    r: f32
    g: f32
    b: f32
    a: f32

impl Color:
    fn new(r: f32, g: f32, b: f32, a: f32) -> Color
    fn rgb(r: f32, g: f32, b: f32) -> Color
    fn from_hex(hex: u32) -> Color
    fn from_srgb(r: u8, g: u8, b: u8, a: u8) -> Color
    fn to_vec3(self) -> Vec3
    fn to_vec4(self) -> Vec4
    fn lerp(self, other: Color, t: f32) -> Color

    # Presets
    fn white() -> Color
    fn black() -> Color
    fn red() -> Color
    fn green() -> Color
    fn blue() -> Color
```

**Phase 1 Total Lines:** ~700
**Phase 1 Duration:** 1-2 days

---

## Phase 2: Mesh System (Priority: Critical)

**Goal:** Complete mesh representation and primitive generation

### Task 2.1: Complete Mesh Struct
**File:** `simple/std_lib/src/graphics/scene/mesh.spl`
**Depends on:** Phase 1
**Estimated Lines:** 600

```simple
pub struct Mesh:
    vertices: Array[Vertex3D]
    indices: Array[u32]
    bounding_sphere: BoundingSphere
    bounding_box: AABB
    primitive_topology: PrimitiveTopology

pub struct Vertex3D:
    position: Vec3
    normal: Vec3
    tangent: Vec3
    uv: Vec2
    color: Color

pub struct BoundingSphere:
    center: Vec3
    radius: f32

pub struct AABB:
    min: Vec3
    max: Vec3

enum PrimitiveTopology:
    TriangleList
    TriangleStrip
    LineList

impl Mesh:
    # Primitives
    fn create_cube(size: f32) -> Mesh
    fn create_sphere(radius: f32, segments: u32, rings: u32) -> Mesh
    fn create_cylinder(radius: f32, height: f32, segments: u32) -> Mesh
    fn create_cone(radius: f32, height: f32, segments: u32) -> Mesh
    fn create_plane(width: f32, height: f32) -> Mesh
    fn create_quad() -> Mesh

    # Operations
    fn compute_normals(mut self)
    fn compute_tangents(mut self)
    fn compute_bounds(mut self)
    fn get_bounding_sphere(self) -> BoundingSphere
    fn get_bounding_box(self) -> AABB
```

### Task 2.2: Mesh Buffer Types
**File:** `simple/std_lib/src/graphics/render/buffer.spl`
**Depends on:** Task 2.1
**Estimated Lines:** 200

```simple
pub struct VertexBuffer3D:
    buffer: BufferHandle
    vertex_count: u32
    stride: u32

pub struct IndexBuffer3D:
    buffer: BufferHandle
    index_count: u32
    index_type: IndexType

pub struct BufferHandle:
    handle: u64

enum IndexType:
    U16
    U32

impl VertexBuffer3D:
    fn new(vertices: Array[Vertex3D]) -> VertexBuffer3D
    fn upload(mut self, vertices: Array[Vertex3D])
    fn destroy(self)

impl IndexBuffer3D:
    fn new_u32(indices: Array[u32]) -> IndexBuffer3D
    fn destroy(self)
```

**Phase 2 Total Lines:** ~800
**Phase 2 Duration:** 2-3 days

---

## Phase 3: Material System (Priority: Critical)

**Goal:** Implement PBR and basic material system

### Task 3.1: Material Enum and Structs
**File:** `simple/std_lib/src/graphics/scene/material.spl`
**Depends on:** Phase 1, Phase 2
**Estimated Lines:** 500

```simple
pub enum Material:
    PBR(pbr: PBRMaterial)
    Phong(phong: PhongMaterial)
    Unlit(unlit: UnlitMaterial)

pub struct PBRMaterial:
    albedo: Color
    albedo_map: Option[TextureHandle]
    metallic: f32
    roughness: f32
    metallic_roughness_map: Option[TextureHandle]
    normal_map: Option[TextureHandle]
    normal_scale: f32
    ao_map: Option[TextureHandle]
    ao_strength: f32
    emissive: Color
    emissive_map: Option[TextureHandle]
    emissive_intensity: f32
    alpha_mode: AlphaMode
    alpha_cutoff: f32
    double_sided: bool

pub struct PhongMaterial:
    diffuse: Color
    diffuse_map: Option[TextureHandle]
    specular: Color
    specular_map: Option[TextureHandle]
    shininess: f32
    normal_map: Option[TextureHandle]
    alpha: f32
    alpha_mode: AlphaMode

pub struct UnlitMaterial:
    color: Color
    color_map: Option[TextureHandle]
    alpha_mode: AlphaMode

pub enum AlphaMode:
    Opaque
    Mask
    Blend

impl PBRMaterial:
    # Constructors
    fn new() -> PBRMaterial

    # Presets
    fn preset_gold() -> PBRMaterial
    fn preset_silver() -> PBRMaterial
    fn preset_copper() -> PBRMaterial
    fn preset_plastic(color: Color) -> PBRMaterial
    fn preset_metal(roughness: f32) -> PBRMaterial
```

### Task 3.2: Texture System
**File:** `simple/std_lib/src/graphics/render/texture.spl`
**Depends on:** None
**Estimated Lines:** 300

```simple
pub struct Texture2D:
    handle: u64
    width: u32
    height: u32
    format: TextureFormat

pub struct TextureHandle:
    id: u64

pub enum TextureFormat:
    R8
    RG8
    RGBA8
    RGBA16F
    RGBA32F
    Depth24Stencil8
    Depth32F

impl Texture2D:
    fn new(width: u32, height: u32, format: TextureFormat) -> Texture2D
    fn from_file(path: String) -> Result[Texture2D, String]
    fn from_bytes(data: Array[u8], width: u32, height: u32, format: TextureFormat) -> Texture2D
    fn upload(mut self, data: Array[u8])
    fn destroy(self)
    fn get_view(self) -> u64
```

### Task 3.3: Depth Image
**File:** `simple/std_lib/src/graphics/render/texture.spl` (same file)
**Depends on:** Task 3.2
**Estimated Lines:** 100

```simple
pub struct DepthImage:
    handle: u64
    width: u32
    height: u32

impl DepthImage:
    fn new(width: u32, height: u32) -> DepthImage
    fn destroy(self)
    fn get_view(self) -> u64
```

**Phase 3 Total Lines:** ~900
**Phase 3 Duration:** 3-4 days

---

## Phase 4: Lighting System (Priority: High)

**Goal:** Implement directional, point, and spot lights

### Task 4.1: Light Types
**File:** `simple/std_lib/src/graphics/scene/light.spl`
**Depends on:** Phase 1
**Estimated Lines:** 400

```simple
pub enum Light:
    Directional(dir: DirectionalLight)
    Point(point: PointLight)
    Spot(spot: SpotLight)

pub struct DirectionalLight:
    direction: Vec3
    color: Color
    intensity: f32
    cast_shadows: bool

pub struct PointLight:
    position: Vec3
    color: Color
    intensity: f32
    range: f32
    attenuation: Attenuation
    cast_shadows: bool

pub struct SpotLight:
    position: Vec3
    direction: Vec3
    color: Color
    intensity: f32
    range: f32
    inner_cone_angle: f32
    outer_cone_angle: f32
    attenuation: Attenuation
    cast_shadows: bool

pub enum Attenuation:
    None
    Linear
    Quadratic
    Custom(constant: f32, linear: f32, quadratic: f32)

impl DirectionalLight:
    fn new(direction: Vec3, color: Color, intensity: f32) -> DirectionalLight
    fn get_direction(self) -> Vec3
    fn get_color(self) -> Color
    fn get_intensity(self) -> f32

impl PointLight:
    fn new(position: Vec3, color: Color, intensity: f32) -> PointLight
    fn with_range(self, range: f32) -> PointLight
    fn with_attenuation(self, atten: Attenuation) -> PointLight

impl SpotLight:
    fn new(position: Vec3, direction: Vec3, color: Color, intensity: f32) -> SpotLight
    fn with_angles(self, inner: f32, outer: f32) -> SpotLight
    fn with_range(self, range: f32) -> SpotLight
```

### Task 4.2: Lighting Uniform Data
**File:** `simple/std_lib/src/graphics/render/renderer.spl` (update)
**Depends on:** Task 4.1
**Estimated Lines:** 150 (additions)

```simple
struct LightingUniformData:
    # Directional light
    dir_light_direction: Vec3
    _pad0: f32
    dir_light_color: Vec3
    dir_light_intensity: f32

    # Point lights (max 4 for forward rendering)
    point_light_positions: [Vec4; 4]
    point_light_colors: [Vec4; 4]
    point_light_count: u32
    _pad1: [f32; 3]

    # Spot lights (max 4)
    spot_light_positions: [Vec4; 4]
    spot_light_directions: [Vec4; 4]
    spot_light_colors: [Vec4; 4]
    spot_light_angles: [Vec4; 4]
    spot_light_count: u32
    _pad2: [f32; 3]

    # Ambient
    ambient_color: Vec3
    ambient_intensity: f32
```

**Phase 4 Total Lines:** ~550
**Phase 4 Duration:** 2-3 days

---

## Phase 5: Rendering Pipeline (Priority: Critical)

**Goal:** Complete the rendering loop with proper pipeline management

### Task 5.1: Pipeline Types
**File:** `simple/std_lib/src/graphics/render/pipeline.spl`
**Depends on:** Phases 3, 4
**Estimated Lines:** 300

```simple
pub struct Pipeline3D:
    pipeline: PipelineHandle
    layout: PipelineLayout

pub struct PipelineHandle:
    handle: u64

pub struct PipelineLayout:
    descriptor_sets: Array[DescriptorSetLayout]
    push_constant_ranges: Array[PushConstantRange]

impl Pipeline3D:
    fn get_pipeline(self) -> PipelineHandle
    fn destroy(self)

# Pipeline factory functions
pub fn create_pbr_pipeline() -> Pipeline3D
pub fn create_phong_pipeline() -> Pipeline3D
pub fn create_unlit_pipeline() -> Pipeline3D
pub fn create_shadow_pipeline() -> Pipeline3D
```

### Task 5.2: Uniform Buffers
**File:** `simple/std_lib/src/graphics/render/buffer.spl` (update)
**Depends on:** Phase 2
**Estimated Lines:** 200

```simple
pub struct UniformBuffer[T]:
    buffer: BufferHandle
    data: T

impl UniformBuffer[T]:
    fn new() -> UniformBuffer[T]
    fn update(mut self, data: T)
    fn get_buffer(self) -> BufferHandle
    fn destroy(self)

# Camera uniform data
pub struct CameraUniformData:
    view: Mat4
    proj: Mat4
    view_proj: Mat4
    camera_pos: Vec3
    _pad0: f32
```

### Task 5.3: Complete Renderer3D
**File:** `simple/std_lib/src/graphics/render/renderer.spl` (update)
**Depends on:** Tasks 5.1, 5.2
**Estimated Lines:** 400 (additions/updates)

```simple
impl Renderer3D:
    # Update existing render method
    fn render(mut self, scene: Scene, camera: Camera):
        # 1. Begin render pass
        # 2. Update uniforms (camera, lighting)
        # 3. Traverse scene
        # 4. Cull and batch
        # 5. Render batches
        # 6. End render pass

    fn render_node(mut self, node: SceneNode, world_transform: Mat4)
    fn build_camera_uniform(self, camera: Camera) -> CameraUniformData
    fn collect_lighting(self, scene: Scene) -> LightingUniformData
    fn get_or_create_mesh_buffers(mut self, mesh_handle: MeshHandle) -> MeshBuffers
```

### Task 5.4: Device Manager
**File:** `simple/std_lib/src/graphics/render/device_manager.spl` (update)
**Depends on:** None
**Estimated Lines:** 200

```simple
pub struct DeviceHandle:
    device: u64

impl DeviceHandle:
    fn new() -> DeviceHandle
    fn release(self)
    fn get_handle(self) -> u64
```

**Phase 5 Total Lines:** ~1100
**Phase 5 Duration:** 4-5 days

---

## Phase 6: Scene Graph Completion (Priority: High)

**Goal:** Complete scene graph with proper hierarchy and queries

### Task 6.1: Update SceneNode
**File:** `simple/std_lib/src/graphics/scene/node.spl` (update)
**Depends on:** All previous phases
**Estimated Lines:** 200 (additions)

```simple
impl SceneNode:
    # Add missing methods from spec
    fn activate(mut self)
    fn deactivate(mut self)
    fn is_active(self) -> bool
    fn add_tag(mut self, tag: String)
    fn remove_tag(mut self, tag: String)
    fn has_tag(self, tag: String) -> bool
```

### Task 6.2: Update Scene
**File:** `simple/std_lib/src/graphics/scene/node.spl` (same file)
**Depends on:** Task 6.1
**Estimated Lines:** 250 (additions)

```simple
impl Scene:
    # Query methods
    fn find_node_by_name(self, name: String) -> Option[NodeId]
    fn find_nodes_by_tag(self, tag: String) -> Array[NodeId]
    fn find_nodes_with_component[T](self) -> Array[NodeId]

    # Traversal methods
    fn traverse_bfs(self, visitor: fn(NodeId, SceneNode, Mat4))
    fn traverse_dfs(self, visitor: fn(NodeId, SceneNode, Mat4))
```

**Phase 6 Total Lines:** ~450
**Phase 6 Duration:** 2-3 days

---

## Phase 7: Resource Management (Priority: Medium)

**Goal:** Implement resource handles and managers

### Task 7.1: Resource Manager
**File:** `simple/std_lib/src/graphics/resource_manager.spl` (new)
**Depends on:** Phases 2, 3, 4
**Estimated Lines:** 400

```simple
pub struct ResourceManager:
    meshes: ResourceStore[Mesh]
    materials: ResourceStore[Material]
    textures: ResourceStore[Texture2D]
    next_id: u64

pub struct ResourceStore[T]:
    resources: Dict[u64, T]
    ref_counts: Dict[u64, u32]

impl ResourceManager:
    fn new() -> ResourceManager
    fn load_mesh(mut self, mesh: Mesh) -> MeshHandle
    fn load_material(mut self, material: Material) -> MaterialHandle
    fn load_texture(mut self, texture: Texture2D) -> TextureHandle
    fn get_mesh(self, handle: MeshHandle) -> Option[Mesh]
    fn get_material(self, handle: MaterialHandle) -> Option[Material]
    fn get_texture(self, handle: TextureHandle) -> Option[Texture2D]
    fn release_mesh(mut self, handle: MeshHandle)
    fn release_material(mut self, handle: MaterialHandle)
    fn release_texture(mut self, handle: TextureHandle)
```

**Phase 7 Total Lines:** ~400
**Phase 7 Duration:** 2 days

---

## Phase 8: Asset Loaders (Priority: Medium)

**Goal:** Implement OBJ and image loading

### Task 8.1: Image Loader
**File:** `simple/std_lib/src/graphics/loaders/image.spl` (update)
**Depends on:** Phase 3
**Estimated Lines:** 150

```simple
pub fn load_png(path: String) -> Result[Texture2D, String]
pub fn load_jpeg(path: String) -> Result[Texture2D, String]
pub fn load_image(path: String) -> Result[Texture2D, String]  # Auto-detect format

struct ImageData:
    width: u32
    height: u32
    channels: u32
    data: Array[u8]

fn decode_png(bytes: Array[u8]) -> Result[ImageData, String]
fn decode_jpeg(bytes: Array[u8]) -> Result[ImageData, String]
```

### Task 8.2: OBJ Loader
**File:** `simple/std_lib/src/graphics/loaders/obj.spl` (update)
**Depends on:** Phase 2
**Estimated Lines:** 350

```simple
pub struct ObjLoadOptions:
    flip_uvs: bool
    generate_normals: bool
    generate_tangents: bool

pub fn load_obj(path: String, options: ObjLoadOptions) -> Result[Mesh, String]:
    # Parse OBJ file
    # Build vertex and index arrays
    # Optionally generate normals/tangents
    # Return mesh

struct ObjData:
    positions: Array[Vec3]
    normals: Array[Vec3]
    uvs: Array[Vec2]
    faces: Array[ObjFace]

struct ObjFace:
    vertices: Array[ObjVertex]

struct ObjVertex:
    position_index: u32
    normal_index: Option[u32]
    uv_index: Option[u32]
```

**Phase 8 Total Lines:** ~500
**Phase 8 Duration:** 2-3 days

---

## Phase 9: Vulkan FFI Implementation (Priority: Critical)

**Goal:** Implement the Vulkan FFI functions called by the renderer

### Task 9.1: Rendering FFI
**File:** `src/runtime/src/value/vulkan_3d.rs` (new)
**Depends on:** All previous phases
**Estimated Lines:** 1000 (Rust)

```rust
// Framebuffer
#[no_mangle]
pub extern "C" fn rt_vk_create_framebuffer_3d(
    color_view: u64,
    depth_view: u64,
    width: u32,
    height: u32
) -> u64

#[no_mangle]
pub extern "C" fn rt_vk_destroy_framebuffer(framebuffer: u64)

// Render pass
#[no_mangle]
pub extern "C" fn rt_vk_begin_render_pass_3d(
    framebuffer: u64,
    width: u32,
    height: u32,
    clear_color: [f32; 4]
)

#[no_mangle]
pub extern "C" fn rt_vk_end_render_pass()

// Binding
#[no_mangle]
pub extern "C" fn rt_vk_bind_pipeline(pipeline: u64)

#[no_mangle]
pub extern "C" fn rt_vk_bind_uniform_buffer(set: u32, binding: u32, buffer: u64)

#[no_mangle]
pub extern "C" fn rt_vk_bind_vertex_buffer(buffer: u64)

#[no_mangle]
pub extern "C" fn rt_vk_bind_index_buffer(buffer: u64)

// Push constants
#[no_mangle]
pub extern "C" fn rt_vk_push_constants(model: *const f32, normal_matrix: *const f32)

// Draw
#[no_mangle]
pub extern "C" fn rt_vk_draw_indexed(index_count: u32)

// Buffer creation
#[no_mangle]
pub extern "C" fn rt_vk_create_vertex_buffer(
    data: *const u8,
    size: u64
) -> u64

#[no_mangle]
pub extern "C" fn rt_vk_create_index_buffer(
    data: *const u8,
    size: u64
) -> u64

#[no_mangle]
pub extern "C" fn rt_vk_create_uniform_buffer(size: u64) -> u64

#[no_mangle]
pub extern "C" fn rt_vk_update_uniform_buffer(
    buffer: u64,
    data: *const u8,
    size: u64
)

#[no_mangle]
pub extern "C" fn rt_vk_destroy_buffer(buffer: u64)

// Texture creation
#[no_mangle]
pub extern "C" fn rt_vk_create_texture_2d(
    width: u32,
    height: u32,
    format: u32,
    data: *const u8,
    data_size: u64
) -> u64

#[no_mangle]
pub extern "C" fn rt_vk_destroy_texture(texture: u64)

// Pipeline creation
#[no_mangle]
pub extern "C" fn rt_vk_create_graphics_pipeline(
    vertex_shader: *const u8,
    vertex_size: u64,
    fragment_shader: *const u8,
    fragment_size: u64,
    config: *const PipelineConfig
) -> u64

#[no_mangle]
pub extern "C" fn rt_vk_destroy_pipeline(pipeline: u64)
```

### Task 9.2: Device Management FFI
**File:** `src/runtime/src/value/vulkan_3d.rs` (same)
**Depends on:** Task 9.1
**Estimated Lines:** 200 (additions)

```rust
#[no_mangle]
pub extern "C" fn rt_vk_device_create() -> u64

#[no_mangle]
pub extern "C" fn rt_vk_device_destroy(device: u64)

#[no_mangle]
pub extern "C" fn rt_vk_device_wait_idle(device: u64)
```

**Phase 9 Total Lines:** ~1200 (Rust)
**Phase 9 Duration:** 5-7 days

---

## Phase 10: Testing and Examples (Priority: High)

**Goal:** Create comprehensive tests and examples

### Task 10.1: Unit Tests
**File:** `simple/std_lib/test/unit/graphics/**/*.spl` (multiple files)
**Depends on:** All phases
**Estimated Lines:** 800

Test files:
- `math/vector_spec.spl` - Vector operations
- `math/matrix_spec.spl` - Matrix operations
- `math/quaternion_spec.spl` - Quaternion operations
- `math/transform_spec.spl` - Transform composition
- `scene/mesh_spec.spl` - Mesh creation and operations
- `scene/material_spec.spl` - Material properties
- `scene/light_spec.spl` - Light types
- `scene/camera_spec.spl` - Camera projections

### Task 10.2: Integration Tests
**File:** `simple/std_lib/test/integration/graphics/**/*.spl`
**Depends on:** All phases
**Estimated Lines:** 400

- `rendering/simple_scene_spec.spl` - Render basic scene
- `rendering/lighting_spec.spl` - Test lighting
- `rendering/materials_spec.spl` - Test materials
- `loaders/obj_loader_spec.spl` - Test OBJ loading

### Task 10.3: Examples
**File:** `simple/examples/**/*.spl`
**Depends on:** All phases
**Estimated Lines:** 600

Examples:
- `graphics_hello_cube.spl` - Spinning cube with PBR
- `graphics_lighting_demo.spl` - Multiple light types
- `graphics_material_gallery.spl` - Material showcase
- `graphics_mesh_primitives.spl` - All primitive shapes
- Update `graphics_3d_viewport.spl` to use new system

**Phase 10 Total Lines:** ~1800
**Phase 10 Duration:** 3-4 days

---

## Summary

### Total Estimated Lines of Code

| Component | Simple Code | Rust FFI | Total |
|-----------|-------------|----------|-------|
| Phase 1: Foundation | 700 | - | 700 |
| Phase 2: Mesh System | 800 | - | 800 |
| Phase 3: Material System | 900 | - | 900 |
| Phase 4: Lighting | 550 | - | 550 |
| Phase 5: Rendering Pipeline | 1100 | - | 1100 |
| Phase 6: Scene Graph | 450 | - | 450 |
| Phase 7: Resource Management | 400 | - | 400 |
| Phase 8: Asset Loaders | 500 | - | 500 |
| Phase 9: Vulkan FFI | - | 1200 | 1200 |
| Phase 10: Testing & Examples | 1800 | - | 1800 |
| **Total** | **7200** | **1200** | **8400** |

### Timeline Estimates

| Phase | Duration | Dependencies |
|-------|----------|--------------|
| Phase 1 | 1-2 days | None |
| Phase 2 | 2-3 days | Phase 1 |
| Phase 3 | 3-4 days | Phases 1, 2 |
| Phase 4 | 2-3 days | Phase 1 |
| Phase 5 | 4-5 days | Phases 2, 3, 4 |
| Phase 6 | 2-3 days | All previous |
| Phase 7 | 2 days | Phases 2, 3, 4 |
| Phase 8 | 2-3 days | Phases 2, 3 |
| Phase 9 | 5-7 days | All previous |
| Phase 10 | 3-4 days | All previous |
| **Total** | **26-37 days** | |

**Parallelization Opportunities:**
- Phases 3 and 4 can be done in parallel (both depend on Phase 1-2)
- Phase 7 can be done in parallel with Phase 6
- Phase 8 can be done in parallel with Phase 5-6

**Optimistic Timeline:** 20-25 days (with parallelization)
**Realistic Timeline:** 30-35 days

---

## Implementation Order

### Week 1: Foundation and Mesh System
- Days 1-2: Phase 1 (Foundation)
- Days 3-5: Phase 2 (Mesh System)

### Week 2: Materials and Lighting
- Days 6-9: Phase 3 (Material System)
- Days 10-12: Phase 4 (Lighting)

### Week 3: Rendering Pipeline
- Days 13-17: Phase 5 (Rendering Pipeline)
- Days 18-20: Phase 6 (Scene Graph)

### Week 4: Resource Management and Loaders
- Days 21-22: Phase 7 (Resource Management)
- Days 23-25: Phase 8 (Asset Loaders)

### Week 5: Vulkan FFI
- Days 26-32: Phase 9 (Vulkan FFI)

### Week 6: Testing and Polish
- Days 33-36: Phase 10 (Testing & Examples)
- Days 37: Buffer, documentation, bug fixes

---

## Success Criteria

### Phase Completion Criteria

Each phase is considered complete when:
1. All code compiles without errors
2. Unit tests pass (if applicable)
3. Documentation is complete
4. Code review passed (self-review minimum)

### Overall Project Completion

The core 3D engine is complete when:
1. ✅ All 10 phases completed
2. ✅ Can render a scene with:
   - Multiple meshes (cube, sphere, plane)
   - PBR materials
   - Multiple lights (directional, point, spot)
   - Camera controller (FPS)
3. ✅ Scene3D widget works in UI
4. ✅ All unit tests pass
5. ✅ All integration tests pass
6. ✅ All examples run successfully
7. ✅ Performance acceptable (60 FPS for medium complexity scene)

---

## Risk Mitigation

### Technical Risks

1. **Vulkan FFI complexity**
   - Mitigation: Start with simple FFI functions, iterate
   - Fallback: Use existing Vulkan window FFI as reference

2. **Performance issues**
   - Mitigation: Profile early and often
   - Fallback: Implement batching and culling in Phase 5

3. **Shader compilation**
   - Mitigation: Use pre-compiled SPIR-V initially
   - Fallback: Manual GLSL → SPIR-V compilation

### Schedule Risks

1. **Underestimated complexity**
   - Mitigation: Build in 20% buffer time
   - Fallback: Cut non-critical features (shadows, advanced post-processing)

2. **Integration issues**
   - Mitigation: Integration tests early
   - Fallback: Simplify interfaces if needed

---

## Next Steps

1. **Immediate:** Begin Phase 1 (Foundation)
2. **After Phase 1:** Review and adjust plan based on actual implementation time
3. **After Phase 5:** Create minimal working example to validate architecture
4. **After Phase 10:** Create roadmap for advanced features (shadows, deferred, animation)

---

**End of Implementation Plan**
