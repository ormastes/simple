# Design: Driver API Heavy Path Stabilization

**Date:** 2026-03-29
**Requirements:** [driver_api_heavy_path.md](../02_requirements/feature/driver_api_heavy_path.md)
**Plan:** [driver_api_heavy_path_stabilization_plan_2026-03-29.md](../03_plan/driver_api_heavy_path_stabilization_plan_2026-03-29.md)

## Architecture

### Current State (Facade Containment)

```
External caller
  └─ driver_api.spl (thin facade)
       ├─ driver_public_api.spl       → interpret_file, generate_headers (subprocess)
       ├─ driver_public_shared.spl    → aot_shared_library (subprocess)
       ├─ driver_public_compile.spl   → compile_file, aot_c_file, ... (subprocess)
       └─ driver_api_core.spl         → find_runtime_lib_dir, try_load_smf_cached (heavy)
```

Problem: `driver_api_core.spl` imports the full compiler graph at file scope (even with `use lazy`).

### Target State (Tiered Internal)

```
External caller
  └─ driver_api.spl (thin facade, re-exports from tiers)
       ├─ driver_api_types.spl            [tier 0: types + extern fns]
       ├─ driver_api_interpret.spl        [tier 1: interpret_file, try_load_smf_cached]
       ├─ driver_api_compile_single.spl   [tier 2: compile_file, compile_files, check_file, parse_sdn_file]
       ├─ driver_api_codegen_backends.spl [tier 3: aot_c_file, aot_llvm_file, aot_cuda_file, aot_vhdl_file]
       ├─ driver_api_native_single.spl    [tier 4: aot_native_file_with_backend, aot_llvm_native_file]
       ├─ driver_api_project_build.spl    [tier 5: aot_native_project_with_backend]
       ├─ driver_api_headers.spl          [tier 5: generate_headers]
       └─ driver_api_shared_lib.spl       [tier 5: aot_shared_library]

       Lightweight facades remain as subprocess fallback (driver_public_*.spl)
```

### Dependency Rules

- Each tier may only import from lower tiers or from `compiler.driver.driver_core_types`
- Tier 0 imports nothing from the compiler graph
- Tiers 1-2 import `CompilerDriver` and `CompileOptions` only
- Tiers 3-4 add backend-specific imports
- Tier 5 adds linker, header gen, and project-level imports

### Rust Loader Changes

1. **Diagnostics**: `SIMPLE_LOADER_TRACE=1` env var enables structured trace output
2. **Generalized selective filtering**: Remove hardcoded `driver_api.spl` / `driver/__init__.spl` path checks; apply `should_keep_export` logic to all `__init__.spl` files with bare exports when `requested_names` is available
3. **Early termination**: When all requested names have been found in sibling scan, skip remaining siblings

### Package Init Patterns

**Before (bare exports with sibling preloading):**
```simple
# __init__.spl
export symbol_from_sibling_a, symbol_from_sibling_b
```

**After (explicit re-exports):**
```simple
# __init__.spl
export use compiler.driver.driver_api_types.{CompileResult, CompileOptions}
export use compiler.driver.driver_api_interpret.{interpret_file}
```

## Test Strategy

- System tests: import termination, grouped import scope, artifact production
- Rust unit tests: selective import filtering, sibling scanning, diagnostic output
- Regression: any new API module addition must pass import termination test
