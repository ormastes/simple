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

