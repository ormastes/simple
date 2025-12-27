# 3D Graphics and Engine Specification

**Version:** 1.0
**Date:** 2025-12-27
**Status:** Active Specification

## Overview

This document specifies the 3D graphics and engine subsystem for the Simple language. The 3D engine provides a complete scene graph, rendering pipeline, material system, and integration with the Vulkan/SPIR-V backend.

## Design Philosophy

1. **Vulkan-First**: Designed around Vulkan compute and graphics capabilities
2. **PBR-Based**: Physically-Based Rendering as the default material model
3. **Deferred-Capable**: Architecture supports both forward and deferred rendering
4. **ECS-Compatible**: Component system allows future ECS integration
5. **Editor-Friendly**: Designed for both runtime and tooling use
6. **Performance**: GPU-optimized with frustum culling, batching, instancing
7. **Flexible**: Supports both embedded (UI) and standalone rendering

## Related Specifications

- [GPU and SIMD](gpu_simd.md) - Vulkan backend, compute shaders, GPU buffers
- [Types](types.md) - Type system, ownership, mutability
- [Memory](memory.md) - Memory management, resource lifecycle
- [Standard Library](stdlib.md) - Core library APIs

---

## Part 1: Architecture Overview

### 1.1 System Components

```
┌─────────────────────────────────────────────────────────────┐
│                     Application Layer                        │
│  ┌────────────┐  ┌──────────────┐  ┌──────────────────┐    │
│  │   Scene    │  │   Camera     │  │   Controls       │    │
│  │   Setup    │  │  Management  │  │   (FPS/Orbit)    │    │
│  └────────────┘  └──────────────┘  └──────────────────┘    │
└─────────────────────────────────────────────────────────────┘
                            │
┌─────────────────────────────────────────────────────────────┐
│                   Scene Graph Layer                          │
│  ┌──────────┐  ┌───────────┐  ┌───────────┐  ┌──────────┐ │
│  │  Scene   │  │ SceneNode │  │ Transform │  │Component │ │
│  │  Root    │  │ Hierarchy │  │  System   │  │  System  │ │
│  └──────────┘  └───────────┘  └───────────┘  └──────────┘ │
└─────────────────────────────────────────────────────────────┘
                            │
┌─────────────────────────────────────────────────────────────┐
│                  Rendering System Layer                      │
│  ┌────────────┐  ┌──────────┐  ┌─────────────────────┐    │
│  │  Renderer  │  │ Pipeline │  │   Material System   │    │
│  │   3D       │  │ Manager  │  │  (PBR/Phong/Unlit)  │    │
│  └────────────┘  └──────────┘  └─────────────────────┘    │
│  ┌────────────┐  ┌──────────┐  ┌─────────────────────┐    │
│  │  Culling   │  │ Lighting │  │   Shadow Mapping    │    │
│  │   System   │  │  System  │  │   (CSM/VSM/PCF)     │    │
│  └────────────┘  └──────────┘  └─────────────────────┘    │
└─────────────────────────────────────────────────────────────┘
                            │
┌─────────────────────────────────────────────────────────────┐
│                   Resource Layer                             │
│  ┌──────────┐  ┌──────────┐  ┌───────────┐  ┌──────────┐  │
│  │   Mesh   │  │Texture   │  │  Shader   │  │  Buffer  │  │
│  │ Manager  │  │ Manager  │  │  Manager  │  │ Allocator│  │
│  └──────────┘  └──────────┘  └───────────┘  └──────────┘  │
└─────────────────────────────────────────────────────────────┘
                            │
┌─────────────────────────────────────────────────────────────┐
│                 Vulkan Backend Layer                         │
│  ┌──────────────┐  ┌────────────────┐  ┌───────────────┐  │
│  │   Device     │  │  Command       │  │   Swapchain   │  │
│  │   Manager    │  │  Buffers       │  │   Manager     │  │
│  └──────────────┘  └────────────────┘  └───────────────┘  │
│  ┌──────────────┐  ┌────────────────┐  ┌───────────────┐  │
│  │  Descriptor  │  │   Render       │  │   Pipeline    │  │
│  │     Sets     │  │   Passes       │  │    Cache      │  │
│  └──────────────┘  └────────────────┘  └───────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 Coordinate System

- **Right-handed coordinate system**: +X right, +Y up, +Z forward (towards viewer)
- **Camera faces**: -Z direction (OpenGL convention)
- **Rotations**: Counter-clockwise is positive (right-hand rule)
- **Matrices**: Column-major storage (Vulkan/OpenGL convention)
- **Clip space**: Vulkan convention (Y-down, Z [0, 1])

### 1.3 Units and Scales

- **World units**: Meters (1.0 unit = 1 meter)
- **Angles**: Radians internally, degrees in user API
- **Time**: Seconds (f32 delta_time)
- **Light intensity**: Lumens (physically-based)
- **Color space**: Linear RGB internally, sRGB for textures

---

## Part 2: Scene Graph System

### 2.1 Scene Hierarchy

```simple
# Scene - Root container
struct Scene:
    name: String
    root: SceneNode
    resource_manager: ResourceManager
    next_node_id: u64

# SceneNode - Hierarchical transform node
struct SceneNode:
    id: NodeId
    name: String
    transform: Transform           # Local transform (relative to parent)
    components: Array[Component]   # Attached components
    children: Array[NodeId]        # Child node IDs (indices into scene array)
    parent_id: Option[NodeId]      # Parent node ID
    active: bool                   # Enable/disable node
    tags: Set[String]              # User tags for queries
```

**Design Rationale:**
- **ID-based children**: Prevents ownership issues, enables ECS patterns
- **Component array**: Flexible attachment of behavior
- **Tags**: Fast queries for "all enemies", "collectibles", etc.

### 2.2 Transform System

```simple
struct Transform:
    position: Vec3
    rotation: Quaternion
    scale: Vec3

impl Transform:
    # Constructors
    fn identity() -> Transform
    fn new(pos: Vec3, rot: Quaternion, scale: Vec3) -> Transform

    # Transform composition
    fn to_matrix(self) -> Mat4
    fn compose(parent: Transform, child: Transform) -> Transform
    fn inverse(self) -> Transform

    # Transformation operations
    fn translate(self, offset: Vec3) -> Transform
    fn rotate(self, rotation: Quaternion) -> Transform
    fn rotate_euler(self, pitch: f32, yaw: f32, roll: f32) -> Transform
    fn scale_uniform(self, factor: f32) -> Transform
    fn scale_vec3(self, scale: Vec3) -> Transform

    # Direction vectors
    fn forward(self) -> Vec3    # -Z in local space
    fn right(self) -> Vec3      # +X in local space
    fn up(self) -> Vec3         # +Y in local space

    # Look-at
    fn look_at(self, target: Vec3, up: Vec3) -> Transform
```

**Transform Caching:**
- Each node maintains `world_transform_cache: Option[Mat4]`
- Invalidated on local transform change or parent update
- Recomputed lazily during scene traversal

### 2.3 Component System

```simple
enum Component:
    # Rendering
    MeshRenderer(mesh: MeshHandle, material: MaterialHandle)
    SkinnedMeshRenderer(mesh: MeshHandle, material: MaterialHandle, skeleton: SkeletonHandle)

    # Lighting
    Light(light: Light)

    # Camera
    Camera(camera: Camera)

    # Audio
    AudioSource(source: AudioSourceHandle)
    AudioListener

    # Physics (future)
    RigidBody(body: RigidBodyHandle)
    Collider(collider: ColliderHandle)

    # Animation
    Animator(animator: AnimatorHandle)

    # Custom
    Script(script: ScriptHandle)
    Custom(name: String, data: Any)

# Component queries
impl SceneNode:
    fn get_component[T](self) -> Option[T]
    fn get_components[T](self) -> Array[T]
    fn add_component(mut self, component: Component)
    fn remove_component[T](mut self) -> Option[T]
```

**Design Principles:**
- **Enum-based**: Type-safe component access
- **Handle-based resources**: Enables resource sharing and management
- **Query by type**: Pattern matching for component access

### 2.4 Scene Queries

```simple
impl Scene:
    # Find nodes
    fn find_node_by_name(self, name: String) -> Option[NodeId]
    fn find_nodes_by_tag(self, tag: String) -> Array[NodeId]
    fn find_nodes_with_component[T](self) -> Array[NodeId]

    # Traversal
    fn traverse(self, visitor: fn(NodeId, SceneNode, Mat4))
    fn traverse_bfs(self, visitor: fn(NodeId, SceneNode, Mat4))
    fn traverse_dfs(self, visitor: fn(NodeId, SceneNode, Mat4))

    # Spatial queries (with bounding volumes)
    fn find_in_frustum(self, frustum: Frustum) -> Array[NodeId]
    fn find_in_sphere(self, center: Vec3, radius: f32) -> Array[NodeId]
    fn find_in_box(self, aabb: AABB) -> Array[NodeId]

    # Lifecycle
    fn activate_node(mut self, id: NodeId)
    fn deactivate_node(mut self, id: NodeId)
    fn destroy_node(mut self, id: NodeId)
```

---

## Part 3: Rendering Pipeline

### 3.1 Render Passes

The engine supports multiple rendering strategies:

#### Forward Rendering (Default)

```
1. Shadow Pass (directional/spot lights)
   ├─ Depth-only render to shadow maps
   └─ Store in shadow atlas

2. Opaque Pass
   ├─ Frustum culling
   ├─ Z-prepass (optional, for complex scenes)
   ├─ Opaque geometry (front-to-back)
   └─ Lighting (per-object or per-pixel)

3. Transparent Pass
   ├─ Transparent geometry (back-to-front)
   └─ Blending enabled

4. Post-Processing (optional)
   ├─ Bloom
   ├─ Tone mapping
   ├─ FXAA/SMAA
   └─ Color grading
```

#### Deferred Rendering (Advanced)

```
1. Shadow Pass
   └─ Same as forward

2. G-Buffer Pass
   ├─ Render to MRT: Albedo, Normal, Material, Depth
   └─ Store per-pixel geometry data

3. Lighting Pass
   ├─ Full-screen quad
   ├─ Compute lighting from G-Buffer
   └─ Support 100+ lights efficiently

4. Forward+ Pass (for transparent objects)
   └─ Light culling + forward shading

5. Post-Processing
   └─ Same as forward
```

### 3.2 Rendering Configuration

```simple
enum RenderMode:
    Forward
    ForwardPlus
    Deferred

struct RenderSettings:
    mode: RenderMode
    msaa: u32                      # 1, 2, 4, 8
    vsync: bool
    shadow_quality: ShadowQuality  # Low, Medium, High, Ultra
    max_lights: u32                # 4 (forward), 256 (deferred)
    bloom_enabled: bool
    fxaa_enabled: bool
    tone_mapping: ToneMapping      # None, Reinhard, ACES, Filmic

struct Renderer3D:
    device: DeviceHandle
    settings: RenderSettings
    pipelines: PipelineCache
    shadow_mapper: ShadowMapper
    gbuffer: Option[GBuffer]       # For deferred rendering
```

### 3.3 Culling System

```simple
# Frustum culling
struct Frustum:
    planes: [Plane; 6]  # Left, Right, Top, Bottom, Near, Far

impl Frustum:
    fn from_view_proj(view_proj: Mat4) -> Frustum
    fn contains_sphere(self, center: Vec3, radius: f32) -> bool
    fn contains_aabb(self, aabb: AABB) -> bool

# Bounding volumes
struct AABB:
    min: Vec3
    max: Vec3

struct BoundingSphere:
    center: Vec3
    radius: f32

# Culling pass
fn cull_scene(scene: Scene, camera: Camera) -> Array[NodeId]:
    let frustum = Frustum::from_view_proj(camera.get_view_projection_matrix())
    let mut visible = Array::new()

    scene.traverse(\id, node, world_transform:
        if let Some(renderer) = node.get_component[MeshRenderer]():
            let bounds = renderer.mesh.get_bounding_sphere()
            let world_center = world_transform.transform_point(bounds.center)
            if frustum.contains_sphere(world_center, bounds.radius):
                visible.push(id)
    )

    return visible
```

### 3.4 Draw Call Batching

```simple
# Batch key for grouping draw calls
struct BatchKey:
    pipeline: u64
    material: u64
    mesh: u64

impl BatchKey:
    fn hash(self) -> u64

# Batching system
struct DrawBatch:
    key: BatchKey
    instances: Array[InstanceData]

struct InstanceData:
    world_matrix: Mat4
    normal_matrix: Mat3
    material_params: MaterialParams

fn batch_draw_calls(visible_nodes: Array[NodeId], scene: Scene) -> Array[DrawBatch]:
    let mut batches: Dict[BatchKey, DrawBatch] = Dict::new()

    for id in visible_nodes:
        let node = scene.get_node(id)
        let renderer = node.get_component[MeshRenderer]().unwrap()

        let key = BatchKey {
            pipeline: renderer.material.get_pipeline(),
            material: renderer.material.get_id(),
            mesh: renderer.mesh.get_id()
        }

        if not batches.contains_key(key):
            batches.insert(key, DrawBatch { key: key, instances: Array::new() })

        batches.get_mut(key).instances.push(InstanceData {
            world_matrix: node.get_world_transform(),
            normal_matrix: node.get_world_transform().to_mat3().transpose(),
            material_params: renderer.material.get_params()
        })

    return batches.values().collect()
```

---

## Part 4: Material System

### 4.1 Material Types

```simple
enum Material:
    # Physically-Based Rendering
    PBR(pbr: PBRMaterial)

    # Classic Phong (legacy, simple)
    Phong(phong: PhongMaterial)

    # Unlit (no lighting)
    Unlit(unlit: UnlitMaterial)

    # Custom shader
    Custom(shader: ShaderHandle, params: MaterialParams)
```

### 4.2 PBR Material (Default)

**Standard PBR Material:**

```simple
struct PBRMaterial:
    # Base properties
    albedo: Color                    # Base color (sRGB)
    albedo_map: Option[TextureHandle]

    # Metallic workflow
    metallic: f32                    # 0.0 = dielectric, 1.0 = metal
    roughness: f32                   # 0.0 = smooth, 1.0 = rough
    metallic_roughness_map: Option[TextureHandle]  # R=unused, G=roughness, B=metallic

    # Normal mapping
    normal_map: Option[TextureHandle]
    normal_scale: f32                # Normal map strength

    # Ambient occlusion
    ao_map: Option[TextureHandle]
    ao_strength: f32

    # Emission
    emissive: Color
    emissive_map: Option[TextureHandle]
    emissive_intensity: f32

    # Additional maps
    height_map: Option[TextureHandle]
    height_scale: f32                # For parallax mapping

    # Rendering flags
    alpha_mode: AlphaMode            # Opaque, Mask, Blend
    alpha_cutoff: f32                # For alpha masking
    double_sided: bool

enum AlphaMode:
    Opaque      # No transparency
    Mask        # Binary alpha (cutoff)
    Blend       # Smooth blending

impl PBRMaterial:
    # Presets (common materials)
    fn preset_gold() -> PBRMaterial
    fn preset_silver() -> PBRMaterial
    fn preset_copper() -> PBRMaterial
    fn preset_aluminum() -> PBRMaterial
    fn preset_plastic(color: Color) -> PBRMaterial
    fn preset_wood() -> PBRMaterial
    fn preset_metal(roughness: f32) -> PBRMaterial
```

**PBR Shader (GLSL-like pseudocode):**

```glsl
// Vertex shader outputs
struct VertexOutput {
    vec4 position;       // Clip space position
    vec3 world_pos;      // World space position
    vec3 world_normal;   // World space normal
    vec3 world_tangent;  // For normal mapping
    vec3 world_bitangent;
    vec2 uv;             // Texture coordinates
};

// Fragment shader
vec3 pbr_shading(VertexOutput input, PBRMaterial mat, vec3 view_dir) {
    // Sample textures
    vec3 albedo = mat.albedo.rgb;
    if (mat.albedo_map.is_some()) {
        albedo *= texture(mat.albedo_map, input.uv).rgb;
        albedo = srgb_to_linear(albedo);  // Convert to linear space
    }

    float metallic = mat.metallic;
    float roughness = mat.roughness;
    if (mat.metallic_roughness_map.is_some()) {
        vec2 mr = texture(mat.metallic_roughness_map, input.uv).gb;
        roughness *= mr.x;
        metallic *= mr.y;
    }

    // Normal mapping
    vec3 N = normalize(input.world_normal);
    if (mat.normal_map.is_some()) {
        vec3 tangent_normal = texture(mat.normal_map, input.uv).xyz * 2.0 - 1.0;
        tangent_normal.xy *= mat.normal_scale;
        mat3 TBN = mat3(input.world_tangent, input.world_bitangent, N);
        N = normalize(TBN * tangent_normal);
    }

    // Ambient occlusion
    float ao = 1.0;
    if (mat.ao_map.is_some()) {
        ao = texture(mat.ao_map, input.uv).r;
        ao = mix(1.0, ao, mat.ao_strength);
    }

    // PBR lighting calculation
    vec3 F0 = mix(vec3(0.04), albedo, metallic);
    vec3 Lo = vec3(0.0);

    // Iterate over lights
    for (Light light in scene_lights) {
        vec3 L = normalize(light.direction);  // Or point light direction
        vec3 H = normalize(view_dir + L);
        float distance = length(light.position - input.world_pos);
        float attenuation = 1.0 / (distance * distance);
        vec3 radiance = light.color * light.intensity * attenuation;

        // Cook-Torrance BRDF
        float NDF = DistributionGGX(N, H, roughness);
        float G = GeometrySmith(N, view_dir, L, roughness);
        vec3 F = FresnelSchlick(max(dot(H, view_dir), 0.0), F0);

        vec3 numerator = NDF * G * F;
        float denominator = 4.0 * max(dot(N, view_dir), 0.0) * max(dot(N, L), 0.0) + 0.0001;
        vec3 specular = numerator / denominator;

        vec3 kS = F;
        vec3 kD = vec3(1.0) - kS;
        kD *= 1.0 - metallic;

        float NdotL = max(dot(N, L), 0.0);
        Lo += (kD * albedo / PI + specular) * radiance * NdotL;
    }

    // Ambient
    vec3 ambient = vec3(0.03) * albedo * ao;
    vec3 color = ambient + Lo;

    // Emissive
    vec3 emissive = mat.emissive.rgb * mat.emissive_intensity;
    if (mat.emissive_map.is_some()) {
        emissive *= texture(mat.emissive_map, input.uv).rgb;
    }
    color += emissive;

    return color;
}
```

### 4.3 Phong Material (Legacy)

```simple
struct PhongMaterial:
    # Diffuse
    diffuse: Color
    diffuse_map: Option[TextureHandle]

    # Specular
    specular: Color
    specular_map: Option[TextureHandle]
    shininess: f32

    # Ambient (legacy, usually replaced by scene ambient)
    ambient: Color

    # Normal map
    normal_map: Option[TextureHandle]

    # Alpha
    alpha: f32
    alpha_mode: AlphaMode

impl PhongMaterial:
    fn preset_emerald() -> PhongMaterial
    fn preset_ruby() -> PhongMaterial
    fn preset_pearl() -> PhongMaterial
```

### 4.4 Unlit Material

```simple
struct UnlitMaterial:
    color: Color
    color_map: Option[TextureHandle]
    alpha_mode: AlphaMode
```

### 4.5 Material Parameters

```simple
# Runtime material parameters (for GPU uniforms)
struct MaterialParams:
    albedo: Vec4              # RGB + alpha
    metallic: f32
    roughness: f32
    emissive_intensity: f32
    normal_scale: f32
    ao_strength: f32
    alpha_cutoff: f32
    _pad: f32

# Descriptor set layout for materials
#[descriptor_set(set=1)]
struct MaterialDescriptors:
    #[binding(0)] params: UniformBuffer[MaterialParams]
    #[binding(1)] albedo_map: Texture2D
    #[binding(2)] normal_map: Texture2D
    #[binding(3)] metallic_roughness_map: Texture2D
    #[binding(4)] ao_map: Texture2D
    #[binding(5)] emissive_map: Texture2D
    #[binding(6)] sampler: Sampler
```

---

## Part 5: Lighting System

### 5.1 Light Types

```simple
enum Light:
    Directional(dir: DirectionalLight)
    Point(point: PointLight)
    Spot(spot: SpotLight)
    Area(area: AreaLight)  # Future: rectangle, disk lights

# Directional light (sun, moon)
struct DirectionalLight:
    direction: Vec3      # World space direction (normalized)
    color: Color         # Light color (linear RGB)
    intensity: f32       # Illuminance in lux
    cast_shadows: bool

impl DirectionalLight:
    fn new(direction: Vec3, color: Color, intensity: f32) -> DirectionalLight

# Point light (bulb, torch)
struct PointLight:
    position: Vec3       # World space position
    color: Color
    intensity: f32       # Luminous intensity in candelas
    range: f32           # Max distance (for culling)
    attenuation: Attenuation
    cast_shadows: bool

enum Attenuation:
    None              # No falloff (unrealistic)
    Linear            # Linear falloff
    Quadratic         # Physically accurate (inverse square)
    Custom(constant: f32, linear: f32, quadratic: f32)

impl PointLight:
    fn with_range(self, range: f32) -> PointLight
    fn with_attenuation(self, atten: Attenuation) -> PointLight

    # Presets
    const Range16: f32 = 16.0
    const Range32: f32 = 32.0
    const Range64: f32 = 64.0

# Spot light (flashlight, stage light)
struct SpotLight:
    position: Vec3
    direction: Vec3      # World space direction
    color: Color
    intensity: f32
    range: f32
    inner_cone_angle: f32  # Radians
    outer_cone_angle: f32  # Radians
    attenuation: Attenuation
    cast_shadows: bool

impl SpotLight:
    fn with_angles(self, inner: f32, outer: f32) -> SpotLight
    fn with_range(self, range: f32) -> SpotLight
```

### 5.2 Shadow Mapping

```simple
enum ShadowQuality:
    Low      # 512x512, 1 cascade
    Medium   # 1024x1024, 2 cascades
    High     # 2048x2048, 4 cascades
    Ultra    # 4096x4096, 4 cascades with PCF

# Shadow mapper
struct ShadowMapper:
    atlas: Texture2DArray     # Shadow atlas (2D array texture)
    cascades: u32             # For CSM (Cascaded Shadow Maps)
    pcf_enabled: bool         # Percentage Closer Filtering
    bias: f32                 # Shadow acne prevention

impl ShadowMapper:
    fn render_shadows(self, scene: Scene, lights: Array[Light])
    fn get_shadow_matrix(self, light_index: u32, cascade: u32) -> Mat4
    fn sample_shadow(self, world_pos: Vec3, light_index: u32) -> f32
```

### 5.3 Lighting Uniforms

```simple
# Per-frame lighting data (descriptor set 0, binding 1)
struct LightingUniformData:
    # Directional light
    dir_light_direction: Vec3
    _pad0: f32
    dir_light_color: Vec3
    dir_light_intensity: f32

    # Point lights (max 4 in forward, 256 in deferred)
    point_light_positions: [Vec4; 4]    # w = range
    point_light_colors: [Vec4; 4]       # rgb = color, a = intensity
    point_light_count: u32
    _pad1: [f32; 3]

    # Spot lights (max 4)
    spot_light_positions: [Vec4; 4]
    spot_light_directions: [Vec4; 4]
    spot_light_colors: [Vec4; 4]        # rgb = color, a = intensity
    spot_light_angles: [Vec4; 4]        # x = inner, y = outer, z = range
    spot_light_count: u32
    _pad2: [f32; 3]

    # Ambient lighting
    ambient_color: Vec3
    ambient_intensity: f32

    # Shadow matrices
    shadow_matrices: [Mat4; 8]          # Max 8 shadow-casting lights
```

---

## Part 6: Mesh and Geometry System

### 6.1 Mesh Representation

```simple
struct Mesh:
    vertices: VertexBuffer3D
    indices: IndexBuffer3D
    bounding_sphere: BoundingSphere
    bounding_box: AABB
    primitive_topology: PrimitiveTopology

enum PrimitiveTopology:
    TriangleList
    TriangleStrip
    LineList
    LineStrip
    PointList

# Vertex layout
struct Vertex3D:
    position: Vec3      # Object space position
    normal: Vec3        # Object space normal
    tangent: Vec3       # For normal mapping
    uv: Vec2            # Texture coordinates
    color: Color        # Vertex color (optional)

impl Mesh:
    # Primitive generation
    fn create_cube(size: f32) -> Mesh
    fn create_sphere(radius: f32, segments: u32, rings: u32) -> Mesh
    fn create_cylinder(radius: f32, height: f32, segments: u32) -> Mesh
    fn create_cone(radius: f32, height: f32, segments: u32) -> Mesh
    fn create_torus(major_radius: f32, minor_radius: f32, major_seg: u32, minor_seg: u32) -> Mesh
    fn create_plane(width: f32, height: f32) -> Mesh
    fn create_quad() -> Mesh  # Full-screen quad for post-processing

    # Mesh operations
    fn compute_normals(mut self)
    fn compute_tangents(mut self)
    fn compute_bounds(mut self)
    fn optimize(mut self)  # Vertex cache optimization

    # Loading
    fn from_obj(path: String) -> Result[Mesh, String]
    fn from_gltf(path: String) -> Result[Array[Mesh], String]
```

### 6.2 Vertex and Index Buffers

```simple
struct VertexBuffer3D:
    buffer: BufferHandle
    vertex_count: u32
    stride: u32

impl VertexBuffer3D:
    fn new(vertices: Array[Vertex3D]) -> VertexBuffer3D
    fn from_mesh(mesh: Mesh) -> VertexBuffer3D
    fn upload(mut self, vertices: Array[Vertex3D])
    fn get_buffer(self) -> BufferHandle

struct IndexBuffer3D:
    buffer: BufferHandle
    index_count: u32
    index_type: IndexType

enum IndexType:
    U16
    U32

impl IndexBuffer3D:
    fn new_u16(indices: Array[u16]) -> IndexBuffer3D
    fn new_u32(indices: Array[u32]) -> IndexBuffer3D
    fn from_mesh(mesh: Mesh) -> IndexBuffer3D
```

### 6.3 Mesh Loaders

```simple
# OBJ loader
mod loaders.obj:
    struct ObjLoadOptions:
        flip_uvs: bool
        generate_normals: bool
        generate_tangents: bool

    fn load(path: String, options: ObjLoadOptions) -> Result[Mesh, String]

# glTF 2.0 loader
mod loaders.gltf:
    struct GltfScene:
        meshes: Array[Mesh]
        materials: Array[Material]
        textures: Array[Texture]
        nodes: Array[SceneNode]

    fn load(path: String) -> Result[GltfScene, String]
    fn load_embedded(data: Array[u8]) -> Result[GltfScene, String]
```

---

## Part 7: Camera System

### 7.1 Camera Types

```simple
struct Camera:
    projection: Projection
    transform: Transform  # Camera position and rotation
    view_cache: Option[Mat4]
    proj_cache: Option[Mat4]

enum Projection:
    Perspective(fov: Radians, aspect: f32, near: f32, far: f32)
    Orthographic(left: f32, right: f32, bottom: f32, top: f32, near: f32, far: f32)

impl Camera:
    # Standard constructors
    fn perspective_standard(aspect: f32) -> Camera  # 90° FOV, near=0.1, far=100
    fn orthographic_standard(width: f32, height: f32) -> Camera

    # Matrix access
    fn get_view_matrix(mut self) -> Mat4
    fn get_projection_matrix(mut self) -> Mat4
    fn get_view_projection_matrix(mut self) -> Mat4

    # Ray casting (for picking)
    fn screen_to_ray(self, screen_pos: Vec2, viewport_size: Vec2) -> Ray

struct Ray:
    origin: Vec3
    direction: Vec3  # Normalized

impl Ray:
    fn intersect_plane(self, plane: Plane) -> Option[Vec3]
    fn intersect_sphere(self, center: Vec3, radius: f32) -> Option[f32]
    fn intersect_aabb(self, aabb: AABB) -> Option[f32]
```

### 7.2 Camera Controllers

```simple
# FPS camera controller
struct FpsCamera:
    camera: Camera
    move_speed: f32
    look_sensitivity: f32
    pitch: f32  # Radians
    yaw: f32    # Radians
    min_pitch: f32  # -89 degrees
    max_pitch: f32  # +89 degrees

impl FpsCamera:
    fn update(mut self, delta_time: f32, input: CameraInput)
    fn move_forward(mut self, delta_time: f32)
    fn move_backward(mut self, delta_time: f32)
    fn move_right(mut self, delta_time: f32)
    fn move_left(mut self, delta_time: f32)
    fn move_up(mut self, delta_time: f32)
    fn move_down(mut self, delta_time: f32)
    fn look(mut self, delta_x: f32, delta_y: f32)

# Orbit camera controller
struct OrbitCamera:
    camera: Camera
    target: Vec3
    distance: f32
    rotation: Vec2  # Azimuth, elevation
    zoom_speed: f32
    orbit_speed: f32

impl OrbitCamera:
    fn update(mut self, input: CameraInput)
    fn orbit(mut self, delta_azimuth: f32, delta_elevation: f32)
    fn zoom(mut self, delta: f32)
    fn pan(mut self, delta_x: f32, delta_y: f32)
```

---

## Part 8: Resource Management

### 8.1 Resource Handles

```simple
# Handle types (opaque IDs for resource management)
struct MeshHandle:
    id: u64

struct MaterialHandle:
    id: u64

struct TextureHandle:
    id: u64

struct ShaderHandle:
    id: u64

impl Handle:
    fn new(id: u64) -> Self
    fn invalid() -> Self
    fn is_valid(self) -> bool
```

### 8.2 Resource Manager

```simple
struct ResourceManager:
    meshes: ResourceStore[Mesh]
    materials: ResourceStore[Material]
    textures: ResourceStore[Texture]
    shaders: ResourceStore[Shader]

struct ResourceStore[T]:
    resources: Dict[u64, T]
    next_id: u64
    ref_counts: Dict[u64, u32]

impl ResourceStore[T]:
    fn new() -> ResourceStore[T]
    fn load(mut self, resource: T) -> u64
    fn get(self, id: u64) -> Option[T]
    fn get_mut(mut self, id: u64) -> Option[&mut T]
    fn release(mut self, id: u64)
    fn inc_ref(mut self, id: u64)
    fn dec_ref(mut self, id: u64) -> u32  # Returns new ref count
```

### 8.3 Asset Loading

```simple
# Async loading (future)
struct AssetLoader:
    worker_pool: ThreadPool
    pending_loads: Dict[String, LoadStatus]

enum LoadStatus:
    Pending
    Loading(progress: f32)
    Complete(handle: u64)
    Failed(error: String)

impl AssetLoader:
    fn load_async[T](mut self, path: String, callback: fn(Result[T, String]))
    fn load_sync[T](self, path: String) -> Result[T, String]
    fn get_status(self, path: String) -> LoadStatus
```

---

## Part 9: Shader System

### 9.1 Shader Stages

```simple
struct Shader:
    vertex: ShaderModule
    fragment: ShaderModule
    geometry: Option[ShaderModule]
    tessellation_control: Option[ShaderModule]
    tessellation_evaluation: Option[ShaderModule]

struct ShaderModule:
    spirv: Array[u8]     # SPIR-V bytecode
    entry_point: String  # "main" by default
```

### 9.2 Shader Compilation

```simple
# Compile GLSL to SPIR-V
mod shaders:
    fn compile_glsl(source: String, stage: ShaderStage) -> Result[ShaderModule, String]
    fn load_spirv(path: String) -> Result[ShaderModule, String]

    enum ShaderStage:
        Vertex
        Fragment
        Geometry
        TessellationControl
        TessellationEvaluation
        Compute
```

### 9.3 Standard Shaders

The engine provides built-in shaders:

- **pbr.vert** / **pbr.frag** - PBR material shading
- **phong.vert** / **phong.frag** - Phong shading
- **unlit.vert** / **unlit.frag** - Unlit rendering
- **shadow_depth.vert** / **shadow_depth.frag** - Shadow map generation
- **skybox.vert** / **skybox.frag** - Skybox rendering
- **post_process.vert** / **tonemap.frag** - Tone mapping
- **post_process.vert** / **bloom.frag** - Bloom effect

---

## Part 10: Integration with UI System

### 10.1 Scene3D Widget

The `Scene3D` widget embeds a 3D viewport in the 2D UI:

```simple
use ui.widget.Scene3D

struct Scene3D:
    id: ElementId
    scene: Scene
    camera: Camera
    renderer: Renderer3D
    controls: Option[CameraControls]
    width: u32
    height: u32

enum CameraControls:
    FPS(fps: FpsCamera)
    Orbit(orbit: OrbitCamera)
    None

impl Scene3D:
    fn new(id: ElementId, width: u32, height: u32) -> Scene3D
    fn with_scene(mut self, scene: Scene) -> Scene3D
    fn with_camera(mut self, camera: Camera) -> Scene3D
    fn with_controls(mut self) -> Scene3D  # Default FPS controls
    fn with_orbit_controls(mut self) -> Scene3D
    fn to_element(self) -> Element
```

**Rendering Integration:**

```simple
impl Widget for Scene3D:
    fn layout(mut self, constraints: BoxConstraints) -> Size

    fn paint(mut self, ctx: PaintContext):
        # Render 3D scene to texture
        self.renderer.render(self.scene, self.camera)

        # Get rendered texture
        let texture = self.renderer.get_render_target().get_color_texture()

        # Draw texture to 2D canvas
        ctx.draw_texture(texture, Rect::new(0.0, 0.0, self.width, self.height))

    fn handle_event(mut self, event: Event) -> EventResult:
        match event:
            case Event::MouseMove(x, y):
                if let Some(CameraControls::FPS(fps)) = self.controls:
                    fps.look(x, y)
            # ... handle WASD keys, etc.
```

---

## Part 11: Performance Optimization

### 11.1 Instancing

```simple
# Render many copies of the same mesh efficiently
struct InstancedMesh:
    mesh: MeshHandle
    material: MaterialHandle
    instances: Array[Mat4]  # Per-instance transforms

impl Renderer3D:
    fn render_instanced(self, instanced: InstancedMesh):
        # Upload instance data to GPU
        let instance_buffer = create_instance_buffer(instanced.instances)

        # Draw with instancing
        vk_draw_indexed_instanced(
            instanced.mesh.get_index_count(),
            instanced.instances.len()
        )
```

### 11.2 Level of Detail (LOD)

```simple
struct LODMesh:
    lod_levels: Array[Mesh]  # Decreasing detail
    distances: Array[f32]    # Distance thresholds

impl LODMesh:
    fn select_lod(self, camera_distance: f32) -> Mesh:
        for i in 0..self.distances.len():
            if camera_distance < self.distances[i]:
                return self.lod_levels[i]
        return self.lod_levels.last()
```

### 11.3 Occlusion Culling

```simple
# GPU-based occlusion queries
struct OcclusionQuery:
    query_pool: QueryPool
    results: Array[bool]

impl OcclusionQuery:
    fn begin_query(self, index: u32)
    fn end_query(self, index: u32)
    fn get_result(self, index: u32) -> bool  # Is visible?
```

---

## Part 12: Animation System (Future)

### 12.1 Skeletal Animation

```simple
struct Skeleton:
    bones: Array[Bone]
    bind_poses: Array[Mat4]
    inverse_bind_poses: Array[Mat4]

struct Bone:
    name: String
    parent: Option[u32]  # Bone index
    transform: Transform

struct AnimationClip:
    name: String
    duration: f32
    channels: Array[AnimationChannel]

struct AnimationChannel:
    bone_index: u32
    position_keys: Array[(f32, Vec3)]  # Time, position
    rotation_keys: Array[(f32, Quaternion)]
    scale_keys: Array[(f32, Vec3)]

struct Animator:
    skeleton: Skeleton
    current_clip: Option[AnimationClip]
    time: f32
    bone_matrices: Array[Mat4]  # Final bone transforms

impl Animator:
    fn play(mut self, clip: AnimationClip)
    fn update(mut self, delta_time: f32)
    fn get_bone_matrix(self, bone_index: u32) -> Mat4
```

---

## Part 13: Post-Processing Effects

### 13.1 Tone Mapping

```simple
enum ToneMapping:
    None
    Reinhard
    ReinhardLuminance
    ACES
    Filmic
    Uncharted2

impl Renderer3D:
    fn apply_tone_mapping(self, hdr_color: Vec3, mode: ToneMapping) -> Vec3
```

### 13.2 Bloom

```simple
struct BloomSettings:
    enabled: bool
    threshold: f32
    intensity: f32
    blur_passes: u32

impl Renderer3D:
    fn render_bloom(self, scene_texture: Texture, settings: BloomSettings) -> Texture
```

### 13.3 Anti-Aliasing

```simple
enum AntiAliasing:
    None
    FXAA
    SMAA(quality: SMAQuality)
    TAA  # Temporal Anti-Aliasing

enum SMAAQuality:
    Low
    Medium
    High
    Ultra
```

---

## Part 14: Debug Rendering

### 14.1 Debug Draw API

```simple
struct DebugDraw:
    lines: Array[DebugLine]
    boxes: Array[DebugBox]
    spheres: Array[DebugSphere]

struct DebugLine:
    start: Vec3
    end: Vec3
    color: Color

struct DebugBox:
    min: Vec3
    max: Vec3
    color: Color

struct DebugSphere:
    center: Vec3
    radius: f32
    color: Color

impl DebugDraw:
    fn draw_line(mut self, start: Vec3, end: Vec3, color: Color)
    fn draw_box(mut self, aabb: AABB, color: Color)
    fn draw_sphere(mut self, center: Vec3, radius: f32, color: Color)
    fn draw_frustum(mut self, frustum: Frustum, color: Color)
    fn draw_axis(mut self, transform: Mat4, size: f32)
    fn clear(mut self)
    fn render(self, view_proj: Mat4)  # Call after main scene rendering
```

---

## Part 15: Example Usage

### 15.1 Basic 3D Scene

```simple
use graphics.*
use graphics.math.*
use graphics.scene.*
use graphics.render.*

fn main():
    # Create scene
    let mut scene = Scene::new("My Scene")

    # Create cube mesh
    let cube_mesh = scene.resource_manager.load_mesh(Mesh::create_cube(1.0))
    let cube_material = scene.resource_manager.load_material(
        Material::PBR(PBRMaterial::preset_gold())
    )

    # Create scene node
    let cube_node = scene.create_node("Cube")
    scene.get_node_mut(cube_node).set_transform(
        Transform::new()
            .with_position(Vec3::new(0.0, 0.0, 0.0))
            .with_rotation(Quaternion::from_euler(0.0, 0.0, 0.0))
    )
    scene.get_node_mut(cube_node).add_component(
        Component::MeshRenderer(cube_mesh, cube_material)
    )

    # Add light
    let light_node = scene.create_node("Sun")
    scene.get_node_mut(light_node).add_component(
        Component::Light(Light::Directional(
            DirectionalLight::new(
                Vec3::new(-0.5, -1.0, -0.3).normalize(),
                Color::white(),
                1.5
            )
        ))
    )

    # Create camera
    let camera = Camera::perspective_standard(16.0 / 9.0)
        .with_position(Vec3::new(0.0, 2.0, 5.0))
        .look_at(Vec3::zero(), Vec3::unit_y())

    # Create renderer
    let mut renderer = Renderer3D::new(1920, 1080)

    # Render
    renderer.render(scene, camera)
```

### 15.2 Scene with UI Integration

```simple
use ui.*
use graphics.*

fn build_ui(tree: &mut ElementTree) -> Element:
    let scene = create_game_scene()
    let camera = create_game_camera()

    return Column::new(tree.alloc_id())
        .child(
            Scene3D::new(tree.alloc_id(), 1280, 720)
                .with_scene(scene)
                .with_camera(camera)
                .with_controls()
                .to_element()
        )
        .to_element()

fn main():
    let mut app = Application::new("Game")
        .window_size(1280, 720)

    app.set_root(build_ui(&mut app.element_tree))
    app.run()
```

---

## Part 16: Implementation Roadmap

### Phase 1: Core Rendering (Current State)
- [x] Math primitives (Vec2, Vec3, Vec4, Mat3, Mat4)
- [x] Transform system
- [x] Scene graph structure
- [x] Basic renderer architecture
- [x] Vulkan backend integration
- [ ] Complete mesh loading (OBJ, glTF)
- [ ] Texture loading (PNG, JPEG)
- [ ] Basic material system

### Phase 2: PBR and Lighting
- [ ] PBR material implementation
- [ ] PBR shader (vertex + fragment)
- [ ] Directional/point/spot lights
- [ ] Shadow mapping (CSM)
- [ ] Normal mapping
- [ ] Environment mapping (IBL)

### Phase 3: Optimization
- [ ] Frustum culling
- [ ] Draw call batching
- [ ] Instancing support
- [ ] LOD system
- [ ] Occlusion culling

### Phase 4: Advanced Features
- [ ] Skeletal animation
- [ ] Post-processing (bloom, tone mapping, AA)
- [ ] Particle systems
- [ ] Deferred rendering
- [ ] Debug rendering

### Phase 5: Tooling
- [ ] Scene editor
- [ ] Material editor
- [ ] Shader hot-reload
- [ ] Performance profiler

---

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
