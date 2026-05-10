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

