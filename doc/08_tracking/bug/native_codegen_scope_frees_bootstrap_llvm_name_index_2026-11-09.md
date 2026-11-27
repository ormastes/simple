# Native codegen: per-module transient scope frees the bootstrap LLVM name index ("rejected invalid array handle")

- **Severity:** P2. Common root cause of the MCP native build (windows_mcp_native_build_blocked_at_hir_entry_2026-09-01), the CUDA-port build (cuda_optimizer_surface_owner_2026_10_10), and the HashMap receiver repro.
- **Status:** fix-implemented-verification-pending
- **Found:** 2026-11-09, `C:/dev/p3new/stage2new/stage2_new4.exe`, Windows x86_64

## Repro (minimal)
`test/s3sanity/w5_use_io_runtime.spl` (a one-line `use std.io_runtime` entry), built with the s3sanity case
runner (in-process route: `SIMPLE_FILE_WORKERS=0`, `--entry-closure`, `--source src/lib`). stderr:
```
[simple-runtime][error] rejected invalid array handle before dereference; probable compiler/FFI ABI mismatch (value_bits=0x000001e6e1be1021)
```
## Root cause (lldb, attached to the native-build worker child)
Breakpoint on the report's `fprintf`. The stack, symbolized from raw return addresses:
```
rt_core_report_invalid_array_once <- rt_typed_words_i64_at
<- compiler__mir___MirLowering__bootstrap_globals__bootstrap_llvm_exact_function_index + 223
<- MirToLlvm.bootstrap_llvm_function_index_for_name <- MirToLlvm.lookup_function_return_type
<- translate_operand_at <- translate_call_at <- translate_instruction_at <- translate_block_at
<- translate_function_with_ir_handle(_impl) <- translate_function <- translate_module_with_entry_policy
```
`bootstrap_llvm_exact_function_index` reads the module-global `[i64]` tables
`_bootstrap_llvm_exact_key_*` / `_bootstrap_llvm_base_key_*`. `bootstrap_llvm_name_index_ensure()` builds those
tables lazily, and treats them as valid while `(epoch, function count)` is unchanged. The first build happens
inside the per-module LLVM codegen transient scope (`llvm_codegen_adapter.spl` / `backend_helpers.spl`
`compile_module_with_backend_scoped_v1`, opened with `transient_scope_begin()`). When that scope ends, the tables
are freed. The next module's lookup passes the epoch/count check and dereferences a freed, unregistered array.
The runtime guard rejects it and returns 0, so the lookups silently fail.

## Fix
Warm the index (`bootstrap_llvm_name_index_ensure()`) before `transient_scope_begin()` at both scoped codegen
sites. This follows the same pattern as the tool-discovery caches that are already warmed there.
**Remaining limit:** if the MIR function count grows *after* the warm-up (for example in pipelined lowering),
`ensure` rebuilds inside a scope again. If that turns out to happen, the next step is to build the index under
`rt_session_alloc_begin`.

## Evidence still missing
A native "after" run needs a stage2 rebuilt from this change. That build was not done in this lane.
