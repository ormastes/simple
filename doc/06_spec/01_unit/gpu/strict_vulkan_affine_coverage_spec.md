# Strict Vulkan affine coverage rectangle

Executable source: `test/01_unit/lib/gc_async_mut/gpu/engine2d/strict_vulkan_affine_coverage_spec.spl`

## Requirement

`REQ-2D-002`: DrawIR v4 affine geometry must reach an Engine2D Vulkan compute
shader as a local rectangle and local-to-surface matrix. For `coverage-aa`,
each target pixel receives the area of the transformed parallelogram inside
its unit pixel square. Surface-space clipping is applied before dispatch.
An opaque source is composited with sRGB encoded, premultiplied SrcOver over
the already opaque framebuffer. The shader paints one polygon per dispatch,
so two triangle halves cannot double blend their shared diagonal.

## Scenarios

1. A 45-degree local rectangle produces an opaque interior, an untouched
   clipped exterior, and a partial-coverage edge. The pixels must come from
   the strict device readback with a positive device and submission identity.
2. A later singular affine record rejects the entire composition before any
   strict submit or fence, even after an earlier valid affine record.
3. An affine rectangle carrying an image URI rejects before shader admission;
   the coverage shader must never silently ignore another DrawIR payload.

## Evidence status

The SPIR-V shader is generated from
`src/lib/gc_async_mut/gpu/engine2d/shaders/affine_coverage_rect.comp`. Its
f32 coefficients are admitted only after bounded f64 preflight. The focused
spec has not been run on a Vulkan device, so exact Skia edge parity and
physical case 02 qualification remain unproven. Missing Vulkan hardware is
an explicit test failure, not a passing skip.
