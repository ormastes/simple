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

