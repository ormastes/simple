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

