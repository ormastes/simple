# SPIR-V Boundary — Candidate Builder vs. glslangValidator

> The board Vulkan plan names `vulkan.shader.spirv_binary@1` as the first

<details>
<summary>Full Scenario Manual</summary>

# SPIR-V Boundary — Candidate Builder vs. glslangValidator

The board Vulkan plan names `vulkan.shader.spirv_binary@1` as the first

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver / counterpart conformance |
| Status | In Progress |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/spirv_boundary_glslang_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The board Vulkan plan names `vulkan.shader.spirv_binary@1` as the first
counterpart boundary every SoC lane must clear, host-only, before any GPU is
involved. This spec answers the question that boundary exists to ask: does
`compiler.backend.vulkan.spirv_builder.SpirvBuilder` — the only Simple source
that emits SPIR-V — produce a module byte-for-byte equivalent (after honest
canonicalization) to what an independent, Khronos-authored reference compiler
(`glslangValidator`) produces for the same shader.

## Scope and Preconditions

Host-only, no GPU. Requires `/usr/bin/glslangValidator`, `/usr/bin/spirv-as`,
`/usr/bin/spirv-dis`, and `/usr/bin/spirv-val` to be installed; a missing tool
reports the source as `unavailable`, not a pass.

## Primary Workflow

Build the smallest legal compute shader through `SpirvBuilder`'s own public
API, assemble it with `spirv-as`, validate it with `spirv-val`, and
disassemble it back with `spirv-dis`. Compile the semantically equivalent
one-line GLSL compute shader with `glslangValidator`, validate, and
disassemble it the same way. Canonicalize both disassemblies
(`boundary_spirv_canonicalize.spirv_canonical_text` — strips ONLY an explicit
allowlist of debug opcodes, then renumbers ids) and compare.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Candidate | `SpirvBuilder`, driven directly (no GLSL front end exists in Simple) |
| Counterpart | `/usr/bin/glslangValidator`, `process_bridge`, group `khronos-glslang` |
| Canonicalization | Two named dimensions ONLY: debug-opcode allowlist, id renumbering |
| Standing guard | Both captured modules must pass `spirv-val` before any diff runs |
| Sabotage | Flipping the candidate's Z workgroup size literal from 1 to 2 |

## Related Specifications

- [Board Vulkan counterpart plans](board_vulkan_counterpart_plan_spec.spl) — the plan/profile layer this boundary belongs to

## Evidence and Provenance

Executable against the real installed toolchain on this host; the artifact
hash registered for `glslang` in `spirv_glslang_manifest` is the SHA-256 of
the actual `/usr/bin/glslangValidator` binary invoked, not a fabricated value.

## Recovery and Troubleshooting

A red on "agrees with glslang on the minimal module" means the candidate
builder emitted something outside the two allowed canonicalization
dimensions — a real SPIR-V encoder divergence. Fix the builder or narrow the
canonicalizer's honesty, never widen a dimension to hide the diff. This spec
previously shipped a canonicalizer that stripped any instruction whose result
id looked unreferenced, which silently deleted a live `OpLabel` and a live
`OpExtInstImport`. That filter is gone; see
boundary_spirv_canonicalize.spl's module docstring and the two "closes the
hole" scenarios below, which exist specifically to keep it from coming back.

## Compatibility and Limitations

`SpirvBuilder` has no GLSL/HLSL front end, so this spec drives it directly at
the instruction level, deliberately mirroring glslang's unconditional
`gl_WorkGroupSize` builtin-composite encoding rather than relying on the
canonicalizer to erase it.


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>
