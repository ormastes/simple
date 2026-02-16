# Examples Folder Reorganization Plan

**Date:** 2026-02-16
**Status:** Planning
**Files:** 209 files across ~25 directories

## Current Problems

1. **67 loose files at root** - Should be organized into subdirectories
2. **`test_*` prefix abuse** - 20+ files prefixed `test_` (experiments, not examples)
3. **Duplicate formats** - Many files have both `.spl` and `.smf` versions
4. **Category overlap** - GPU/CUDA/Torch, Async/Actors, Pure/Runtime variants
5. **Mixed complexity** - Simple demos mixed with full projects (medgemma_korean)
6. **Inconsistent naming** - Some use `_demo.spl`, some use `_example.spl`, some neither

## Proposed Structure

### Tier 1: User-Facing Examples (By Topic)

```
examples/
├── 01_getting_started/          # NEW - First examples for new users
│   ├── hello_world.spl
│   ├── hello_native.spl
│   ├── basic_syntax.spl
│   └── README.md
│
├── 02_language_features/        # MERGE language_features/ + blocks/ + parser/
│   ├── blocks/
│   │   ├── custom_blocks.spl
│   │   └── user_defined_blocks.spl
│   ├── polymorphism/
│   │   └── static_polymorphism.spl
│   ├── aop/
│   │   └── aspect_oriented.spl
│   ├── syntax/
│   │   ├── async_syntax.spl
│   │   ├── attribute_syntax.spl
│   │   └── spawn_syntax.spl
│   ├── execution_context.spl
│   ├── lean_blocks.spl
│   └── README.md
│
├── 03_concurrency/              # MERGE actors/ + async/ + root async files
│   ├── async_basics.spl
│   ├── async_structure.spl
│   ├── actor_basics.spl
│   ├── concurrency_modes.spl
│   └── README.md
│
├── 04_data_formats/             # NEW - Data serialization/parsing
│   ├── sdn_parser.spl
│   ├── cbor_encoding.spl
│   └── README.md
│
├── 05_stdlib/                   # NEW - Standard library examples
│   ├── platform_library.spl
│   ├── string_operations.spl
│   ├── array_operations.spl
│   └── README.md
│
├── 06_io/                       # EXPAND file_io/ + root I/O demos
│   ├── file/
│   │   ├── file_staging.spl
│   │   └── file_staging_parallel.spl
│   ├── network/
│   │   └── http_client.spl
│   ├── graphics/
│   │   ├── graphics2d.spl
│   │   └── window_creation.spl
│   ├── multimedia/
│   │   ├── audio_playback.spl
│   │   └── gamepad_input.spl
│   └── README.md
│
├── 07_ml/                       # MERGE pure_nn/ + torch/ + root ML files
│   ├── pure_nn/
│   │   ├── 01_basics/
│   │   │   ├── autograd.spl
│   │   │   ├── simple_regression.spl
│   │   │   └── xor_minimal.spl
│   │   ├── 02_layers/
│   │   │   ├── nn_layers.spl
│   │   │   └── layer_composition.spl
│   │   ├── 03_training/
│   │   │   ├── xor_training.spl
│   │   │   ├── iris_classification.spl
│   │   │   └── minibatch_sgd.spl
│   │   ├── 04_complete/
│   │   │   └── full_pipeline.spl
│   │   ├── runtime_compatible/    # Runtime variants (no generics)
│   │   │   ├── autograd_runtime.spl
│   │   │   ├── nn_layers_runtime.spl
│   │   │   ├── xor_training_runtime.spl
│   │   │   └── README_RUNTIME.md
│   │   └── README.md
│   ├── torch/
│   │   ├── basics/
│   │   ├── training/
│   │   ├── inference/
│   │   ├── data/
│   │   ├── advanced/
│   │   └── README.md
│   └── README.md
│
├── 08_gpu/                      # MERGE cuda/ + gpu/ + gpu_patterns/
│   ├── cuda/
│   │   ├── basic.spl
│   │   ├── vectorized.spl
│   │   └── README.md
│   ├── patterns/
│   │   ├── device_enum.spl
│   │   ├── enum_as_index.spl
│   │   ├── type_inference.spl
│   │   └── user_gpu_enum.spl
│   ├── pipelines/
│   │   ├── async_pipeline.spl
│   │   ├── training_pipeline.spl
│   │   └── context_basic.spl
│   └── README.md
│
├── 09_embedded/                 # RENAME baremetal/ + qemu/ + vhdl/
│   ├── baremetal/
│   │   ├── architectures/
│   │   │   ├── x86_64/
│   │   │   ├── arm/
│   │   │   ├── arm64/
│   │   │   ├── riscv32/
│   │   │   └── riscv64/
│   │   ├── blinky_stm32f4.spl
│   │   ├── timer_riscv32.spl
│   │   └── README.md
│   ├── qemu/
│   │   └── unified_runner.spl
│   ├── vhdl/
│   │   ├── alu.spl
│   │   ├── counter.spl
│   │   ├── fsm.spl
│   │   └── README.md
│   └── README.md
│
├── 10_tooling/                  # NEW - Development tools
│   ├── debugging/
│   │   └── factorial_debug.spl
│   ├── testing/
│   │   └── test_attributes.spl
│   ├── backends/
│   │   ├── backend_switching.spl
│   │   ├── jit_compiler.spl
│   │   └── interpreter_modes.spl
│   ├── libraries/
│   │   ├── create_library.spl
│   │   ├── link_libraries.spl
│   │   └── load_from_library.spl
│   └── README.md
│
├── 11_advanced/                 # NEW - Compiler internals
│   ├── optimization/
│   │   ├── opt_before.spl
│   │   └── opt_after.spl
│   ├── mir/
│   │   ├── mir_serialization.spl
│   │   └── mir_json.spl
│   ├── type_inference/
│   │   └── type_inference_demo.spl
│   └── README.md
│
├── experiments/                 # NEW - All test_* files (WIP)
│   ├── autograd/
│   │   ├── test_autograd.spl
│   │   ├── test_autograd_debug.spl
│   │   ├── test_autograd_global.spl
│   │   ├── test_autograd_manual.spl
│   │   ├── test_autograd_store.spl
│   │   └── test_jit_autograd.spl
│   ├── mutability/
│   │   ├── test_mutability.spl
│   │   ├── test_reference.spl
│   │   └── test_array_mutability.spl
│   ├── runtime/
│   │   ├── test_runtime_builtins.spl
│   │   ├── test_import.spl
│   │   └── test_jit_backend.spl
│   ├── simple_math_test.spl
│   ├── todo_fixed_demo.spl
│   └── README.md (mark as experiments)
│
└── projects/                    # Full-scale projects
    └── medgemma_korean/
        ├── src/
        ├── config/
        ├── models/
        ├── research/
        └── README.md
```

### File Mappings (67 root files → Organized)

**01_getting_started/ (3 files)**
- `hello_native.spl` → `01_getting_started/hello_native.spl`
- NEW: `hello_world.spl` (create simple version)
- NEW: `basic_syntax.spl` (create comprehensive syntax demo)

**02_language_features/ (11 files)**
- `blocks/custom_blocks_examples.spl` → `blocks/custom_blocks.spl`
- `blocks/user_defined_block_demo.spl` → `blocks/user_defined_blocks.spl`
- `language_features/static_polymorphism.spl` → `polymorphism/static_polymorphism.spl`
- `language_features/aop_demo.spl` → `aop/aspect_oriented.spl`
- `language_features/execution_context_demo.spl` → `execution_context.spl`
- `language_features/lean_block_demo.spl` → `lean_blocks.spl`
- `language_features/concurrency_modes.spl` → MOVE to `03_concurrency/`
- `parser/async_syntax_example.spl` → `syntax/async_syntax.spl`
- `parser/attribute_syntax_example.spl` → `syntax/attribute_syntax.spl`
- `parser/spawn_syntax_example.spl` → `syntax/spawn_syntax.spl`

**03_concurrency/ (4 files)**
- `async_demo.spl` → `async_basics.spl` (rename)
- `async_structure_demo.spl` → `async_structure.spl`
- `actors/actor_basics.spl` → `actor_basics.spl`
- `language_features/concurrency_modes.spl` → `concurrency_modes.spl`

**04_data_formats/ (2 files)**
- `sdn_parser_usage.spl` → `sdn_parser.spl`
- `cbor_demo.spl` → `cbor_encoding.spl`

**05_stdlib/ (1 file)**
- `platform_library_example.spl` → `platform_library.spl`

**06_io/ (7 files)**
- `file_io/file_staging.spl` → `file/file_staging.spl`
- `file_io/file_staging_parallel.spl` → `file/file_staging_parallel.spl`
- `http_demo.spl` → `network/http_client.spl`
- `graphics2d_demo.spl` → `graphics/graphics2d.spl`
- `window_demo.spl` → `graphics/window_creation.spl`
- `audio_demo.spl` → `multimedia/audio_playback.spl`
- `gamepad_demo.spl` → `multimedia/gamepad_input.spl`

**07_ml/ (35 files - pure_nn + torch)**
- `pure_nn/` restructure into 4 levels + runtime_compatible/
- `torch/` keep existing structure
- `bcrypt_demo.spl` → DELETE or move to experiments (not ML)
- `perf_demo.spl` → DELETE or move to 10_tooling/
- `physics_rapier2d_demo.spl` → DELETE or move to experiments

**08_gpu/ (12 files)**
- `cuda/*.spl` → `cuda/`
- `gpu_patterns/*.spl` → `patterns/`
- `gpu/*.spl` → `pipelines/`

**09_embedded/ (40+ files)**
- `baremetal/` → keep, organize by architecture
- `qemu/` → keep
- `vhdl/` → keep

**10_tooling/ (10 files)**
- `debugging/factorial_debug.spl` → `debugging/`
- `testing/test_attributes_example.spl` → `testing/test_attributes.spl`
- `backend_switching.spl` → `backends/backend_switching.spl`
- `jit_demo.spl` → `backends/jit_compiler.spl`
- `interpreter_demo.spl` → `backends/interpreter_modes.spl`
- `lib_smf/*.spl` → `libraries/`
- `pure_runtime_demo.spl` → `backends/pure_runtime.spl`
- `pure_simple_demo.spl` → `backends/pure_simple.spl`
- `real_impl_demo.spl` → `backends/real_impl.spl`
- `unified_execution_demo.spl` → `backends/unified_execution.spl`

**11_advanced/ (6 files)**
- `opt_before.spl` → `optimization/opt_before.spl`
- `opt_after.spl` → `optimization/opt_after.spl`
- `test_mir_json_simple.spl` → `mir/mir_json.spl`
- `test_mir_serialization.spl` → `mir/mir_serialization.spl`
- `type_inference_demo.spl` → `type_inference/type_inference_demo.spl`
- `lexer_test.spl` → DELETE (internal test)

**experiments/ (20+ files)**
- All `test_autograd*.spl` → `autograd/`
- All `test_mutability*.spl` → `mutability/`
- All `test_runtime*.spl` → `runtime/`
- `test_db_validation_demo.spl` → root
- `todo_fixed_demo.spl` → root
- `simple_math_test.spl` → root
- `native_v2_test.spl` → runtime/
- `native_advanced.spl` → runtime/

**projects/ (1 project)**
- `medgemma_korean/` → keep as-is

**DELETE candidates (duplicates/obsolete):**
- All `.smf` files that have `.spl` equivalents (keep .spl only)
- `torch_demo_fallback.spl` (obsolete fallback)
- `torch_example.spl` (duplicate of torch_demo.spl)
- `debug.wrapper_spec` (internal)
- `cuda.wrapper_spec` (internal)

## Benefits

1. **Clear learning path** - Numbered 01-11 guides progression
2. **Topic-based organization** - Easy to find relevant examples
3. **Separated concerns** - Examples vs Experiments vs Projects
4. **No root clutter** - All files in appropriate subdirectories
5. **Better discoverability** - Each category has README.md
6. **Consistent naming** - Remove `_demo`/`_example` suffixes where redundant

## Migration Steps

1. Create new directory structure
2. Move files according to mapping
3. Update internal paths/imports if needed
4. Add README.md to each top-level category
5. Delete obsolete/duplicate files
6. Update main examples/README.md with new structure
7. Test all examples still run
8. Commit with detailed migration log

## Estimated Impact

- **Files moved:** ~180
- **Files deleted:** ~20 (duplicates)
- **Directories created:** ~40
- **Directories deleted:** ~10
- **READMEs created:** ~12

## Compatibility Notes

- **SMF format deprecation:** Keep only `.spl` versions (delete `.smf` duplicates)
- **Import paths:** Most examples are standalone, minimal impact
- **Test references:** Check if any tests reference `examples/` paths
