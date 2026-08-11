# SPIR-V stage proven conformant against Khronos SPIRV-Tools

**Date:** 2026-08-11
**Boundary:** `vulkan.shader.spirv_binary@1`
**Counterpart:** Khronos SPIRV-Tools v2025.1 (`spirv-as`, `spirv-val`), independence group `khronos-spirv-tools`
**Consequence:** `spirv_implemented` flipped to `true` on all four board-Vulkan backends

This is the first board-Vulkan stage to be earned rather than declared. It matters
because `board_profile_false_claim` refuses `submit` without `spirv`, so every
later stage was gated behind this one.

## The relation was wrong in the plan, and had to be corrected first

`doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md` declared
relation `byte_exact` for this boundary, comparing Simple's output against
glslang's. **That is not a valid oracle.** Two different compilers legitimately
produce different SPIR-V for the same GLSL source, exactly as two DEFLATE encoders
legitimately produce different bytes for the same input. A byte comparison there
would have manufactured false failures and proven nothing. (The same plan states
the compression rule correctly; the SPIR-V boundary simply contradicted it.)

The correct oracle is **normative validation by the reference implementation**:
Khronos `spirv-as` must assemble Simple's assembly, and Khronos `spirv-val` must
validate the resulting binary. Neither tool is ours, neither derives its verdict
from Simple, and both are independent of glslang's compiler front-end — so this is
not circular.

## Evidence

Simple's `SpirvBuilder` emitted this complete module (via its public API only):

```
; SPIR-V
; Version: 1.0
; Generator: Simple Compiler
; Bound: 5
; Schema: 0
OpCapability Shader
OpMemoryModel Logical GLSL450
OpEntryPoint GLCompute %1 "main"
OpExecutionMode %1 LocalSize 1 1 1
%2 = OpTypeVoid
%3 = OpTypeFunction %2
%1 = OpFunction %2 None %3
%4 = OpLabel
OpReturn
OpFunctionEnd
```

Measured exit codes, each captured directly and never through a pipe (a pipe
returns the *last* command's status and has already produced one wrong reading in
this effort):

| Case | Tool | Exit | Meaning |
|---|---|---|---|
| the module above | `spirv-as` | **0** | assembles, 140-byte binary |
| the module above | `spirv-val` | **0** | **validates** |
| `OpReturn` → `OpThisIsNotARealOpcode` | `spirv-as` | **247** | rejected: `Invalid Opcode name` |
| `%1 = OpFunction` → `%9 = OpFunction` | `spirv-as` | 0 | **assembler does NOT catch it** |
| same | `spirv-val` | **1** | rejected: `forward referenced IDs have not been defined: '1[%1]'` |

The last two rows are the negative control, and they carry the real lesson:
`spirv-as` alone is **not** a sufficient oracle. It happily assembles a module
whose entry point names an id nothing defines. Only `spirv-val` catches it. Any
future SPIR-V boundary must validate, not merely assemble.

## An API gap had to be closed to build a valid module at all

`emit_function` mints its own id via `alloc_id()` and returns it, so it cannot be
bound to a pre-allocated entry-point id. But SPIR-V's logical layout requires
`OpEntryPoint` *before* the type declarations, and ids allocate sequentially, so
the entry function's id can be neither known in advance nor predicted. The result
is precisely the failing case in the table: `OpEntryPoint %1` with nothing defining
`%1`.

Closed additively with `emit_function_with_id(id, result_type_id, func_type_id,
control)`. `emit_function` keeps its existing behaviour and every existing caller
is unaffected. Filed separately:
`doc/08_tracking/bug/spirv_builder_emit_function_ignores_preallocated_entry_point_id_2026-08-11.md`.

## What this does and does not license

**Does:** `spirv_implemented = true` on all four backends. The emission is the
shared SoC-neutral core and SPIR-V is architecture-invariant (already enforced by
`boundary_arch.spl`, which treats only this boundary as arch-invariant), so the one
proof covers Adreno, IMG BXE, Intel Gen12 and venus alike.

**Does not:** `submit_implemented` and `readback_implemented` stay `false`, and
`board_runnable_count()` remains **0** — re-verified after the flag change:
`board_vulkan_counterpart_plan_spec.spl` still passes 18/18. A conformant shader
module is not a driver.

## Caveat, stated rather than buried

The proof was obtained by hand via `bin/simple run` plus the real tools, **not**
through a spec. `test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl` exists
but has never produced a non-timeout verdict, because any module touching
`SpirvBuilder` drops to the interpreter at ~100–1000× via an unresolved JIT symbol
— see `spirv_builder_module_drops_to_interpreter_via_unresolved_jit_symbol_2026-08-11.md`.
Until that is fixed, this evidence is reproducible by the transcript above but is
not gated in CI, which is a real weakness of this result.
