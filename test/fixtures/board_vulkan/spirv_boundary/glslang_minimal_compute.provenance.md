# Provenance: `glslang_minimal_compute.spvdis`

**Boundary:** `vulkan.shader.spirv_binary@1`
**Purpose:** committed counterpart reference for
`test/01_unit/os/vulkan/spirv_boundary_glslang_spec.spl`, so the boundary
comparison does not have to shell out to `glslangValidator` on every run (the
process_bridge round trip alone exceeded a 900s test-daemon budget under host
load — see the timing note in the spec's docstring).

## How to regenerate (exact commands, in order)

```sh
mkdir -p /tmp/spirv_fixture
cat > /tmp/spirv_fixture/shader.comp <<'EOF'
#version 450
layout(local_size_x=1, local_size_y=1, local_size_z=1) in;
void main() {}
EOF
glslangValidator -V --target-env vulkan1.0 -S comp \
    -o /tmp/spirv_fixture/glslang.spv /tmp/spirv_fixture/shader.comp
spirv-val /tmp/spirv_fixture/glslang.spv   # must print nothing / exit 0
spirv-dis --no-header /tmp/spirv_fixture/glslang.spv \
    > test/fixtures/board_vulkan/spirv_boundary/glslang_minimal_compute.spvdis
sha256sum /tmp/spirv_fixture/glslang.spv
sha256sum test/fixtures/board_vulkan/spirv_boundary/glslang_minimal_compute.spvdis
```

## Recorded on 2026-08-11

- **Toolchain:** `glslangValidator`, `Glslang Version: 11:15.1.0` (also reports
  `ESSL Version: OpenGL ES GLSL 3.20 glslang Khronos. 15.1.0`, `GLSL Version:
  4.60 glslang Khronos. 15.1.0`, `SPIR-V Version 0x00010600, Revision 1`,
  `GLSL.std.450 Version 100, Revision 1`).
- **Target:** `--target-env vulkan1.0`, stage `comp` (compute).
- **Source shader** (`/tmp/spirv_fixture/shader.comp`):
  ```glsl
  #version 450
  layout(local_size_x=1, local_size_y=1, local_size_z=1) in;
  void main() {}
  ```
- **`spirv-val` on the produced binary:** clean (no output, exit 0) —
  confirmed valid SPIR-V before disassembly.
- **`glslang.spv` SHA-256:**
  `2e20fe5e958e75291419592c6b391fd15efa4a7e22a601b8cd50f6ea144588bf`
- **`glslang_minimal_compute.spvdis` SHA-256:**
  `e4888a2f11deca57e565defbddcb3314e9faf31879bdfd85be6d7ccb951063a4`

## Why this is a real counterpart artifact, not a fabricated one

Every byte in `glslang_minimal_compute.spvdis` originated from `glslangValidator`
compiling the GLSL source above — it was never authored by hand and was never
derived from `spirv_builder.spl`'s own output. `boundary_spirv_provider.spl`
still has a live, exec-backed "regeneration check" scenario
(`spirv_boundary_regenerates_fixture_from_real_glslang`, marked slow) that
re-runs the exact commands above when the toolchain is installed and asserts
the freshly produced disassembly canonicalizes to the same text as this
committed fixture — so drift between the fixture and what glslang actually
emits is a detectable, dated failure rather than a silent staleness.
