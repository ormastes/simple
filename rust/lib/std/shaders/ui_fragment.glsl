#version 450

// Fragment shader for Vulkan UI rendering
// Supports both solid color rendering and textured text rendering

layout(location = 0) in vec2 fragTexCoord;
layout(location = 1) in vec4 fragColor;

layout(location = 0) out vec4 outColor;

layout(binding = 0) uniform sampler2D texSampler;  // Font atlas texture

void main() {
    // Sample from texture (font atlas for text, white texture for solid rects)
    vec4 texColor = texture(texSampler, fragTexCoord);

    // Multiply texture color/alpha by vertex color
    // For solid rectangles: texture is white (1,1,1,1), so outColor = fragColor
    // For text glyphs: texture contains glyph shape, so outColor = fragColor * glyph_alpha
    outColor = fragColor * texColor;

    // Discard fully transparent pixels to avoid writing to depth buffer
    if (outColor.a < 0.01) {
        discard;
    }
}
