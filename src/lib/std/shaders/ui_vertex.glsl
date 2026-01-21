#version 450

// Vertex shader for Vulkan UI rendering
// Converts screen-space coordinates to NDC for GPU rendering

layout(location = 0) in vec2 inPosition;   // Screen coordinates (0..width, 0..height)
layout(location = 1) in vec2 inTexCoord;   // Texture coordinates (0..1)
layout(location = 2) in vec4 inColor;      // RGBA color (0..1)

layout(location = 0) out vec2 fragTexCoord;
layout(location = 1) out vec4 fragColor;

layout(push_constant) uniform PushConstants {
    vec2 screenSize;  // Window dimensions for coordinate conversion
} pc;

void main() {
    // Convert screen coordinates (0..width, 0..height) to NDC (-1..1, -1..1)
    // Y is inverted because Vulkan has top-left origin
    vec2 ndc = (inPosition / pc.screenSize) * 2.0 - 1.0;
    ndc.y = -ndc.y;  // Flip Y axis for Vulkan coordinate system

    gl_Position = vec4(ndc, 0.0, 1.0);

    // Pass through to fragment shader
    fragTexCoord = inTexCoord;
    fragColor = inColor;
}
