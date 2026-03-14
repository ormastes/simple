# SMF Native Build Integration Plan

**Goal:** Wire SMF input resolution into the native build (AOT) pipeline so the
compiler checks backend/options and prefers cached `.smf` modules before falling
back to source `.spl` parsing.

## Current State

- CLI parses `--prefer-smf`, `--no-smf-imports`, `--smf-libs`, `--regenerate-stale-smf`
  into `GlobalFlags` but **never passes them** to compile/run functions.
- `interpret_file_with_smf()` exists but is **never called** from CLI dispatch.
- `cli_run_file()` always calls plain `interpret_file()`.
- `CompileOptions` has `smf_output_mode` for OUTPUT but no fields for INPUT resolution.
- `moduleloader_load_validated()` in 99.loader checks SHB + SMF freshness + options hash
  but is never used by the AOT pipeline.
- Native build `load_sources_impl()` always reads `.spl` from disk.

## Phases

### Phase 1: CompileOptions SMF Input Fields
**File:** `src/compiler/80.driver/driver_types.spl`

Add to `CompileOptions`:
```
prefer_smf: bool           # Prefer cached SMF over source parsing
smf_lib_paths: [text]      # Library search paths for precompiled SMF
regenerate_stale_smf: bool  # Regenerate stale SMF automatically
no_smf_imports: bool        # Disable SMF import resolution entirely
```

Update `CompileOptions.default()` with:
- `prefer_smf: false`
- `smf_lib_paths: []`
- `regenerate_stale_smf: false`
- `no_smf_imports: false`

### Phase 2: CLI Flag Wiring
**Files:** `src/app/cli/main.spl`, `src/app/io/cli_commands.spl`, `src/app/io/cli_compile.spl`

2a. `cli_run_file()` must accept SMF flags and call `interpret_file_with_smf()`
    instead of `interpret_file()` when SMF is enabled.

2b. `cli_compile_pure_simple()` must set the new CompileOptions SMF fields from
    CLI args.

2c. `cli_native_build()` must parse and pass SMF flags to CompileOptions.

2d. `main.spl` dispatch must pass `GlobalFlags` SMF fields through to all
    execution paths (`cli_run_file`, `cli_run_tests`, `cli_compile`, file execution).

### Phase 3: Driver API SMF Entry Points
**File:** `src/compiler/80.driver/driver_api.spl`

3a. Add `compile_files_with_smf()` that:
    - Calls `smf_hooks_init(smf_lib_paths)` when SMF is enabled
    - Sets CompileOptions SMF fields
    - Then calls `CompilerDriver.create(options)` + `run_compile()`

3b. Modify `aot_file()`, `aot_native_file_with_backend()`, etc. to accept
    optional SMF params or create `_with_smf` variants.

### Phase 4: Driver SMF-Aware Source Loading
**File:** `src/compiler/80.driver/driver.spl`

4a. In `load_sources_impl()`, when `options.prefer_smf` is true:
    - For each source file, call `smf_check_freshness()` with options hash
    - If fresh SMF exists and options match, mark module for SMF-path (skip full parse)
    - Track which modules use cached SMF vs source

4b. In `aot_compile()`, for SMF-cached modules:
    - Skip parse → HIR → type-check → MIR pipeline for those modules
    - At link time, include cached `.smf` bytes directly via `link_to_native()`

4c. Use `compute_options_hash()` (already in driver_types.spl) to validate
    that cached SMF was compiled with matching backend/opt_level/release/debug_info.

### Phase 5: Integration
**Files:** `src/compiler/80.driver/driver.spl`, `src/compiler/80.driver/smf_hooks.spl`

5a. Wire `smf_hooks_init()` call in `CompilerDriver.compile()` before
    `load_sources_impl()` when SMF options are set.

5b. Ensure `moduleloader_load_validated()` pattern is used for validated loading
    with options hash check.

## Layer Dependencies

All changes are in layers 80.driver and above (or app/cli) — no cross-layer
violations. The 99.loader `moduleloader_load_validated()` is called from
80.driver which is allowed.

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/80.driver/driver_types.spl` | Add SMF input fields to CompileOptions |
| `src/compiler/80.driver/driver_api.spl` | Add `compile_files_with_smf()` |
| `src/compiler/80.driver/driver.spl` | SMF-aware `load_sources_impl()` + `aot_compile()` |
| `src/app/cli/main.spl` | Pass GlobalFlags SMF fields through dispatch |
| `src/app/io/cli_commands.spl` | `cli_run_file()` uses SMF when enabled |
| `src/app/io/cli_compile.spl` | `cli_compile_pure_simple()` sets SMF options |
