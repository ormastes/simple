# Team 3: Compiler-Backend Refactoring Analysis
## Region: 50.mir / 55.borrow / 60.mir_opt / 70.backend (~253 files, ~68K lines)

---

## 1. FILE_SIZE_VIOLATIONS (>800 lines)

| File | Lines | Proposed Splits |
|------|-------|-----------------|
| `70.backend/backend/mir_to_llvm.spl` | 941 | Split at class boundary ~L65: (1) `mir_to_llvm_core.spl` — MirToLlvm class + translate_module/function/block/terminator (L1-450), (2) `mir_to_llvm_inst.spl` — instruction translation: const/copy/binop/unaryop/call/aggregate/cast/gep/alloc (L451-830), (3) `mir_to_llvm_runtime.spl` — runtime declarations + string globals + cast helpers + inline asm (L830-941) |

---

## 2. WATCH_LIST (600-800 lines)

| File | Lines | Risk |
|------|-------|------|
| `60.mir_opt/optimization_passes.spl` | 779 | Single OptimizationEngine class; split analysis (L184-243) from transforms (L243-560) from DCE (L571-760) |
| `70.backend/backend/cuda_backend.spl` | 756 | Single CudaBackend class; split instruction compilation (L185-500) into `cuda_backend_inst.spl` |
| `70.backend/backend/wasm_backend.spl` | 751 | Contains WasmBackend + WatBuilder + JsGlueGenerator + BrowserBinding — 4 classes. WatBuilder (L245-580, ~50 emit_* methods) should be its own file |
| `70.backend/codegen.spl` | 731 | Near limit; monitor |
| `60.mir_opt/mir_opt/inline.spl` | 721 | 4 classes (InlineCostAnalyzer L65, FunctionInliner L157, FunctionInlining L314, ModuleInliner L529); split ModuleInliner to `module_inliner.spl` |
| `70.backend/backend/cranelift_codegen_adapter.spl` | 697 | Monitor |
| `70.backend/linker/obj_taker.spl` | 679 | Monitor |
| `50.mir/mir_lowering_expr.spl` | 678 | Has layer violation (see below); monitor |
| `70.backend/backend/c_backend_translate.spl` | 676 | Monitor |
| `70.backend/backend/compile_c_entry.spl` | 652 | Monitor |
| `70.backend/backend/llvm_lib_translate_expr.spl` | 646 | Monitor |
| `70.backend/linker/link.spl` | 615 | Monitor |
| `70.backend/backend/vulkan/spirv_builder.spl` | 601 | Monitor |
| `50.mir/mir_lowering.spl` | 600 | Monitor |

---

## 3. DUPLICATION

**Tool status:** `bin/simple duplicate_check` failed (bootstrap binary doesn't recognize the command). Manual analysis follows.

### 3a. Backend Structural Duplication (cuda_backend vs wasm_backend vs c_backend)

All three backends follow the identical MIR visitor pattern:
- `compile(module: MirModule)` — top-level entry
- `compile_function(builder, func)` — per-function
- `compile_instruction(builder, inst)` — match on MirInst variant
- `compile_const`, `compile_copy`, `compile_binop`, `compile_unaryop`, `compile_load`, `compile_store`, `compile_call`, `compile_aggregate`, `compile_get_field`, `compile_set_field`, `compile_cast`

**Resolution:** Extract a `BackendVisitor` trait or mixin with the MIR walk logic. Each backend implements only the `emit_*` primitives. Estimated dedup: ~150-200 lines per backend.

### 3b. WatBuilder Emit Method Repetition

`wasm_backend.spl` lines 245-580: WatBuilder has ~50 `emit_*` methods that are one-liners (`self.emit("instruction")`). Many follow identical patterns (e.g., `emit_i32_add`, `emit_i32_sub`, `emit_i32_mul`, etc.). Could be generated via a table-driven approach or macro.

### 3c. SIMD/Native Byte Encoding

`x86_64_simd.spl` and `encode_riscv32.spl` both use repeated `bytes = bytes + [...]` list concatenation patterns (see Big-O section). Structural duplication in how byte sequences are built.

---

## 4. LAYER_VIOLATIONS

### CRITICAL (upward dependency)

| Source File | Import | Direction | Severity |
|-------------|--------|-----------|----------|
| `50.mir/mir_lowering_expr.spl:17` | `compiler.backend.gpu_intrinsics` | L5 -> L7 | **CRITICAL** — MIR layer depends on backend |
| `70.backend/build_native_pipeline.spl:22-24` | `compiler.driver.driver`, `driver_types`, `driver_api` | L7 -> L8 | **CRITICAL** — Backend depends on driver (3 imports) |
| `70.backend/codegen.spl:616` | `compiler.loader.jit_instantiator` | L7 -> L9.9 | **CRITICAL** — Backend depends on loader |
| `70.backend/backend/jit_interpreter.spl:19` | `compiler.interp.execution.mod` | L7 -> L9.5 | **HIGH** — Backend depends on interpreter |
| `70.backend/backend/llvm_backend_tools.spl:11` | `compiler.interp.interpreter.llvm.tools.*` | L7 -> L9.5 | **HIGH** — Wildcard import of interp utilities |
| `70.backend/backend/wasm_backend.spl:19` | `compiler.interp.interpreter.llvm.tools` | L7 -> L9.5 | **HIGH** — WASM backend depends on interp for tool finding |
| `70.backend/linker/wasm_linker.spl:12` | `compiler.interp.interpreter.llvm.tools` | L7 -> L9.5 | **HIGH** — Linker depends on interp for tool finding |

### Resolution Proposals

1. **`50.mir -> 70.backend`**: Move `gpu_intrinsics.is_gpu_intrinsic()` to `30.types` or `00.common` as a GPU type query utility.
2. **`70.backend -> 95.interp` (tool-finding)**: Extract `find_wat2wasm`, `find_wasm_ld`, `find_wasm_opt`, `find_wasi_sysroot`, and `llvm.tools.*` into a new `70.backend/tool_discovery.spl` or `00.common/tool_finder.spl`. These are just PATH-searching utilities, not interpreter logic.
3. **`70.backend -> 80.driver`**: `build_native_pipeline.spl` should live in `80.driver/` or the driver types should be in a shared lower layer (e.g., `00.common/driver_types.spl`).
4. **`70.backend -> 99.loader`**: The JIT instantiator import in `codegen.spl` is conditional/lazy (line 616, inside a function body). Consider dependency injection.

---

## 5. COUPLING_HOTSPOTS (Fan-out: import count per file)

| Imports | File |
|---------|------|
| 17 | `70.backend/linker/linker_wrapper.spl` |
| 16 | `70.backend/backend/native/mod.spl` |
| 16 | `70.backend/backend/compile_c_entry.spl` |
| 15 | `70.backend/backend/codegen_factory.spl` |
| 14 | `70.backend/build_native_pipeline.spl` |
| 14 | `70.backend/backend/llvm_backend.spl` |
| 13 | `70.backend/build_native.spl` |
| 11 | `60.mir_opt/mir_opt/mod.spl` |

**`linker_wrapper.spl`** (17 imports, 578 lines) is the highest-coupled file. It coordinates linker backends, SMF reading, object resolution, and platform detection — consider splitting into `linker_wrapper_core.spl` and `linker_wrapper_platform.spl`.

### Public API Hotspots (>15 public functions)

| Fns | File |
|-----|------|
| 73 | `70.backend/backend/riscv32_asm.spl` |
| 39 | `70.backend/ffi_minimal.spl` |
| 33 | `70.backend/backend/native/x86_64_simd.spl` |
| 29 | `70.backend/backend/native/mach_inst.spl` |
| 29 | `70.backend/backend/native/elf_writer.spl` |
| 29 | `70.backend/backend/lean_backend.spl` |

**`riscv32_asm.spl`** with 73 public functions is extreme — likely individual instruction encoders that should be grouped into sub-modules (arithmetic, load/store, branch, etc.).

---

## 6. BIGO_FLAGS

### 6a. List Concatenation in Loops (O(n^2) risk)

| File:Line | Pattern | Severity |
|-----------|---------|----------|
| `native/encode_riscv32.spl:420-435` | `hdr = hdr + [bytes...]` x7 in sequence | MEDIUM — sequential, not in loop |
| `native/x86_64_simd.spl:115-263` | `bytes = bytes + [opcode]` x20+ per function | MEDIUM — per-instruction, not hot loop |
| `native/mod.spl:207-275` | `smf = smf + [byte]` x30+ | **HIGH** — building SMF headers byte-by-byte via list concat; use `ByteBuffer.push()` |
| `linker/mold.spl:480` | `all_objects = all_objects + [path]` in loop | MEDIUM — object list typically small |

### 6b. Nested Loops in mir_to_llvm.spl

| Location | Pattern | Severity |
|----------|---------|----------|
| L78+L84 | `for name, body in module.functions` -> `for global_decl in self.string_globals` | MEDIUM — string_globals grows during compilation; O(F*S) |
| L111-112 | `for block in body.blocks` -> `for inst in block.instructions` | LOW — expected MIR traversal pattern |

### 6c. `.contains()` on Lists

| File:Line | Context | Severity |
|-----------|---------|----------|
| `linker/linker_wrapper.spl:496` | `msvc_config.libs.contains(wlib)` | LOW — libs list is small |
| `backend/common/isel_context.spl:95` | `ctx.frame_slots.contains(local_id)` — in instruction selection loop | **MEDIUM** — should use Dict for O(1) lookup |
| `linker/object_resolver.spl:42` | `self.search_paths.contains(path)` | LOW — search paths list is small |
| `linker/smf_getter.spl:108` | `self.search_paths.contains(path)` | LOW — same pattern |

---

## 7. RECOMMENDATIONS (Priority Order)

### P0 — CRITICAL (Layer Violations)
1. **Move `gpu_intrinsics.is_gpu_intrinsic`** from `70.backend` to `00.common` or `30.types` to fix `50.mir -> 70.backend` violation
2. **Extract tool-finding utilities** (`find_wat2wasm`, `find_wasm_ld`, etc.) from `95.interp` to `70.backend/tool_discovery.spl` to fix 4 files' L7->L9.5 violations
3. **Move `build_native_pipeline.spl`** to `80.driver/` or push shared types down to `00.common`

### P1 — HIGH (File Size)
4. **Split `mir_to_llvm.spl`** (941 lines) into 3 files: core, instructions, runtime
5. **Extract `WatBuilder`** from `wasm_backend.spl` into `wasm/wat_builder.spl`
6. **Split `optimization_passes.spl`** into analysis vs. transform vs. DCE

### P2 — MEDIUM (Duplication & Coupling)
7. **Extract `BackendVisitor` trait** for shared MIR walk logic across cuda/wasm/c/llvm backends
8. **Split `riscv32_asm.spl`** (73 public fns) into sub-modules by instruction category
9. **Reduce `linker_wrapper.spl`** fan-out (17 imports) by splitting platform concerns

### P3 — LOW (Performance)
10. **Replace list concat** in `native/mod.spl` SMF header building with `ByteBuffer`
11. **Replace `frame_slots.contains()`** in `isel_context.spl` with Dict lookup
