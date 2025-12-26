# Vulkan UI Shaders

This directory contains SPIR-V shaders for GPU-accelerated UI rendering.

## Required Shaders

### ui_vertex.spv
Vertex shader for UI rendering.

**Input Layout:**
- Location 0: Position (vec2) - Screen coordinates (0..width, 0..height)
- Location 1: TexCoord (vec2) - Texture coordinates (0..1, 0..1)
- Location 2: Color (vec4) - RGBA color (0..1)

**Output:**
- gl_Position - Clip space position
- fragTexCoord - Texture coordinates for fragment shader
- fragColor - Color for fragment shader

**Source (GLSL):**
```glsl
#version 450

layout(location = 0) in vec2 inPosition;
layout(location = 1) in vec2 inTexCoord;
layout(location = 2) in vec4 inColor;

layout(location = 0) out vec2 fragTexCoord;
layout(location = 1) out vec4 fragColor;

layout(push_constant) uniform PushConstants {
    vec2 screenSize;  // Window dimensions
} pc;

void main() {
    // Convert screen coordinates to NDC (-1..1)
    vec2 ndc = (inPosition / pc.screenSize) * 2.0 - 1.0;
    gl_Position = vec4(ndc, 0.0, 1.0);

    fragTexCoord = inTexCoord;
    fragColor = inColor;
}
```

### ui_fragment.spv
Fragment shader for UI rendering with text atlas support.

**Input:**
- fragTexCoord - Texture coordinates
- fragColor - Vertex color

**Uniforms:**
- Texture sampler for font atlas

**Output:**
- outColor - Final RGBA color

**Source (GLSL):**
```glsl
#version 450

layout(location = 0) in vec2 fragTexCoord;
layout(location = 1) in vec4 fragColor;

layout(location = 0) out vec4 outColor;

layout(binding = 0) uniform sampler2D texSampler;

void main() {
    // Sample from font atlas texture
    vec4 texColor = texture(texSampler, fragTexCoord);

    // Multiply texture alpha by vertex color
    // For solid rectangles, texture will be white (1,1,1,1)
    // For text glyphs, texture contains glyph alpha
    outColor = fragColor * texColor;
}
```

## Compilation

To compile these shaders to SPIR-V:

```bash
# Install glslc (part of Vulkan SDK)
# https://vulkan.lunarg.com/sdk/home

# Compile vertex shader
glslc shaders/ui_vertex.glsl -o shaders/ui_vertex.spv

# Compile fragment shader
glslc shaders/ui_fragment.glsl -o shaders/ui_fragment.spv
```

## Integration

The VulkanRenderer loads these shaders in the init() method:

```simple
let shaders = ShaderBuilder::new(&device)
    .vertex_from_file("shaders/ui_vertex.spv")
    .fragment_from_file("shaders/ui_fragment.spv")
    .build()?
```

## Performance Notes

- **Push Constants**: Screen size is passed via push constants for efficient updates
- **Single Texture**: Font atlas texture bound at descriptor set 0, binding 0
- **Alpha Blending**: Fragment shader supports alpha blending for text rendering
- **Solid Rendering**: When texCoord is (0,0) and texture is white, renders solid colored rectangles
- **Text Rendering**: When texCoord maps to glyph in atlas, renders textured text

## Future Enhancements

- SDF (Signed Distance Field) rendering for scalable text
- Multi-texture support for images
- Custom shader effects (blur, glow, shadows)
- 3D transformations (CSS3-style)
