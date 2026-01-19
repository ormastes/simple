# Semantic Duplication Analysis Report

**Date:** 2026-01-19
**Scope:** Full codebase review (Rust + Simple)
**Objective:** Identify semantic duplications and refactoring opportunities

---

## Executive Summary

| Category | Duplicated Lines | Priority |
|----------|-----------------|----------|
| Interpreter/Codegen overlap | 2,600+ | CRITICAL |
| Rust semantic patterns | 1,500+ | HIGH |
| Simple code patterns | 800+ | MEDIUM |
| **Rust → Simple migration candidates** | **1,900** | HIGH |
| **Total refactoring opportunity** | **~6,800 lines** | |

---

## Part 1: Interpreter vs Codegen Duplication (CRITICAL)

The interpreter (`src/compiler/src/interpreter/`) and codegen (`src/compiler/src/codegen/`) paths implement semantically identical logic independently.

### 1.1 Type Conversion Rules (80 lines duplicated)

**Files:**
- `src/compiler/src/value_impl.rs:2-40` - Interpreter type coercion
- `src/compiler/src/codegen/instr/basic_ops.rs:27-65` - Codegen casts

**Duplication:** Both implement:
- Float ↔ Int conversion rules
- Bool coercion (true=1, false=0)
- Truncation/widening semantics

**Fix:** Create `src/compiler/src/type_coercion.rs` with unified rules.

### 1.2 Binary Operations (260 lines duplicated)

**Files:**
- `src/compiler/src/interpreter/expr/ops.rs:47-405`
- `src/compiler/src/codegen/instr/core.rs:13-116`

**Duplicated operations:**
- 20+ BinOp variants with identical dispatch patterns
- Short-circuit evaluation (And/Or)
- Power operation loop construction
- Floor division semantics

**Fix:** Extract `BinOpEvaluator` trait with operation semantics.

### 1.3 Method Dispatch (1,150+ lines duplicated)

**Interpreter:** `src/compiler/src/interpreter_method/` (1000+ lines)
**Codegen:** `src/compiler/src/codegen/instr/methods.rs:77-213`

**Duplicated method routing:**
```
Array:  len, get, set, push, pop, clear, contains, slice
Dict:   len, get, set, clear, keys, values, contains
String: len, concat, contains, slice
```

**Fix:** Create `MethodRegistry` with shared dispatch tables.

### 1.4 Cast Operations (260 lines duplicated)

**Files:**
- `src/compiler/src/interpreter/expr/casting.rs:64-205`
- `src/compiler/src/codegen/llvm/functions/casts.rs`

**Duplicated:** 10 separate `cast_to_*` functions with identical semantics.

**Fix:** Create `CastRules` module with type conversion matrix.

### 1.5 Truthiness Evaluation (80+ lines duplicated)

**Files:**
- `src/compiler/src/value_impl.rs:62-100` (`truthy()`)
- Scattered in `src/compiler/src/codegen/instr/*`

**Duplicated logic:**
```rust
Bool(b) => *b
Int(i) => *i != 0
Float(f) => *f != 0.0
Str(s) => !s.is_empty()
Array(a) => !a.is_empty()
```

**Fix:** Single `is_truthy()` semantic definition.

---

## Part 2: Rust Code Semantic Duplications (HIGH)

### 2.1 Lean Code Generation Visitors (15+ functions)

**Files:**
- `src/compiler/src/codegen/lean/contracts.rs`
- `src/compiler/src/codegen/lean/expressions.rs`
- `src/compiler/src/codegen/lean/types.rs`
- `src/compiler/src/codegen/lean/functions.rs`
- `src/compiler/src/codegen/lean/traits.rs`

**Duplication:** Each implements `to_lean()`, `to_lean_name()` with identical identifier sanitization.

**Fix:** Extract `LeanCodeGen` trait with shared `to_lean_name()` method.

### 2.2 Builder Pattern Classes (200+ lines)

**Files:**
- `src/compiler/src/linker/builder.rs` - LinkerBuilder
- `src/compiler/src/linker/native_binary.rs` - NativeBinaryBuilder

**Overlapping methods:**
```rust
.output(path: impl Into<PathBuf>)
.library(name: impl Into<String>)
.library_path(path: impl Into<PathBuf>)
```

**Fix:** Create `BuilderBase` trait or macro for common patterns.

### 2.3 Error Creation Patterns (670+ occurrences)

**Pattern:** `LowerError::Semantic(format!(...))` repeated everywhere.

**Duplicated messages:**
- `"Cannot resolve module: {}"`
- `"Cannot read module {:?}: {}"`
- `"Cannot parse module {:?}: {}"`

**Fix:** Create error constructor functions in `src/compiler/src/error_factory.rs`.

### 2.4 GPU Dimension Matching (5 identical blocks)

**File:** `src/compiler/src/codegen/llvm/gpu.rs`

**Functions with identical match patterns:**
- `compile_gpu_local_id()`
- `compile_gpu_group_id()`
- `compile_gpu_global_size()`
- `compile_gpu_local_size()`
- `compile_gpu_num_groups()`

**Fix:** Create dimension lookup table:
```rust
const GPU_INTRINSICS: [[&str; 3]; 4] = [
    ["llvm.nvvm.read.ptx.sreg.tid.x", ".y", ".z"],
    // ...
];
```

### 2.5 Type Resolution Matching (30+ branches)

**File:** `src/compiler/src/hir/lower/type_resolver.rs:8-176`

**Pattern:** Repeated recursive match on `Type::*` variants.

**Fix:** Extract type resolution helpers.

---

## Part 3: Simple Code Semantic Duplications (MEDIUM)

### 3.1 Trait Implementations (200+ lines)

**Files:**
- `simple/std_lib/src/core/string_traits.spl:9-56`
- `simple/std_lib/src/core/array.spl:276-319`
- `simple/std_lib/src/core/persistent_list.spl:378-381`

**Duplicated traits:** Clone, Eq, Ord, Hash, Display with identical loop structures.

**Fix:** Create derive-like macros or generic helpers:
```simple
fn generic_eq<T: Eq>(a: &[T], b: &[T]) -> bool:
    if a.len() != b.len(): return false
    for i in 0..a.len():
        if a[i] != b[i]: return false
    true
```

### 3.2 ML/Torch Neural Network Modules (7+ files, ~500 lines)

**Files:** `simple/std_lib/src/ml/torch/nn/`
- `linear.spl`, `conv.spl`, `embedding.spl`, `dropout.spl`, `normalization.spl`

**Duplicated pattern:**
```simple
class Conv2d(Module):
    me __init__(...):
        super().__init__()
        self.handle = @rt_torch_conv2d_new(...)
        if self.handle == 0: panic("...")

    me __del__():
        @rt_torch_module_free(self.handle)

    fn forward(x: Tensor) -> Tensor:
        val handle = @rt_torch_conv2d_forward(self.handle, x.handle)
        Tensor(handle)
```

**Fix:** Create `Module` base with FFI handle management:
```simple
class FFIModule(Module):
    protected handle: i64

    me __del__():
        @rt_torch_module_free(self.handle)

    protected fn check_handle():
        if self.handle == 0: panic("FFI call failed")
```

### 3.3 Vector Math Predicates (60+ methods)

**File:** `simple/std_lib/src/graphics/math/vector.spl`

**Duplicated across Vec2, Vec3, Vec4, Quaternion:**
- `is_zero()`, `is_unit()`, `is_finite()`, `has_nan()`
- `component_min()`, `component_max()`, `clamp()`, `lerp()`

**Fix:** Use trait + generic implementation:
```simple
trait VectorOps<N>:
    fn components() -> [f32; N]

    fn is_zero() -> bool:
        self.components().all(\c: c == 0.0)
```

### 3.4 Collection Methods (150+ lines)

**Files:**
- `simple/std_lib/src/core/array.spl:612-696`
- `simple/std_lib/src/core/persistent_list.spl:242-300`
- `simple/std_lib/src/core/list.spl`

**Duplicated methods:** `all()`, `any()`, `find()`, `count()`, `position()`

**Fix:** Create `Iterable` trait with default implementations.

### 3.5 Primitive Type Extensions (100+ lines)

**File:** `simple/std_lib/src/core/primitives.spl`

**Duplicated between i64 and f64:**
- `is_zero()`, `is_positive()`, `is_negative()`
- `signum()`, `min()`, `max()`, `clamp()`

**Fix:** Use `Number` trait with default implementations.

---

## Part 4: Rust → Simple Migration Candidates

### 4.1 High Priority (1,200+ lines)

| File | Lines | Migration Benefit |
|------|-------|-------------------|
| `src/driver/src/todo_parser.rs` | 608 | Pure string/regex processing |
| `src/common/src/config_env.rs` | 423 | Dictionary manipulation |
| `src/driver/src/cli/test_output.rs` | 410 | Text formatting |

### 4.2 Medium Priority (500+ lines)

| File | Lines | Migration Benefit |
|------|-------|-------------------|
| `src/driver/src/cli/migrate/generics.rs` | 200+ | Character transformation |
| `src/driver/src/cli/help.rs` | 188 | Pure text generation |
| `src/compiler/src/lint/config.rs` | 124 | INI-style parsing |
| `src/driver/src/cli/commands/arg_parsing.rs` | 131 | String flag detection |
| `src/driver/src/cli/sandbox.rs` | 94 | Config parsing |

### 4.3 Migration Strategy

**Phase 1: String Processing**
1. `arg_parsing.rs` functions → Simple CLI module
2. `parse_memory_size()` → Simple stdlib
3. Error message extractors → Simple i18n

**Phase 2: Validation & Config**
1. TODO comment parsing → Simple
2. Lint configuration → Simple
3. Diagram generation args → Simple

**Phase 3: Output Formatting**
1. Test output → Simple
2. Help text → Simple data structures
3. Diagnostic formatting → Simple

---

## Part 5: Recommended Actions

### Immediate (High Impact)

1. **Create `SemanticEvaluator` module** for interpreter/codegen unification
   - Shared `BinOpSemantics`, `UnaryOpSemantics`
   - Unified `TypeCoercion` rules
   - Single `Truthiness` definition

2. **Extract `MethodRegistry`** for method dispatch
   - Shared dispatch tables
   - Both interpreter and codegen use same routing

3. **Migrate `todo_parser.rs` to Simple**
   - Good showcase for Simple's string processing
   - Self-hosting benefit

### Medium Term

4. **Create Simple `FFIModule` base class** for ML layers
   - Eliminate 500+ lines of boilerplate
   - Consistent error handling

5. **Implement `Iterable` trait** with default methods
   - Eliminate 150+ lines of duplicated collection methods

6. **Unify Lean codegen visitors**
   - Single `LeanCodeGen` trait
   - Shared identifier sanitization

### Long Term

7. **Migrate CLI argument parsing to Simple**
   - ~500 lines of string processing
   - Better maintainability

8. **Create derive macros for Simple traits**
   - Auto-generate Clone, Eq, Ord, Hash, Display
   - Reduce boilerplate in stdlib

---

---

## Part 6: Refactoring Actions Completed

### 6.1 Semantics Module Created (Rust)

**Files created:**
- `src/compiler/src/semantics/mod.rs`
- `src/compiler/src/semantics/type_coercion.rs`
- `src/compiler/src/semantics/truthiness.rs`
- `src/compiler/src/semantics/binary_ops.rs`

**Features:**
- `TypeCoercion` - Unified type coercion rules (int/float/bool)
- `TruthinessRules` - Single source of truth for truthiness evaluation
- `BinaryOpSemantics` - Canonical binary operation semantics

**Tests:** 18 unit tests all passing

### 6.2 FFIModule Base Class Created (Simple)

**Files modified:**
- `simple/std_lib/src/ml/torch/nn/base.spl` - Added FFIModule class
- `simple/std_lib/src/ml/torch/nn/linear.spl` - Now uses FFIModule
- `simple/std_lib/src/ml/torch/nn/conv.spl` - Conv2d/Conv3d use FFIModule
- `simple/std_lib/src/ml/torch/nn/dropout.spl` - Dropout uses FFIModule
- `simple/std_lib/src/ml/torch/nn/embedding.spl` - Embedding uses FFIModule
- `simple/std_lib/src/ml/torch/nn/normalization.spl` - BatchNorm1d/2d/LayerNorm use FFIModule
- `simple/std_lib/src/ml/torch/nn/transformer.spl` - MultiheadAttention/Encoder/Decoder use FFIModule
- `simple/std_lib/src/ml/torch/nn/recurrent.spl` - RNN/LSTM/GRU use FFIModule

**Features:**
- `FFIModule(Module)` base class with:
  - `module_handle: u64` field (inherited)
  - `__del__()` method (shared cleanup)
  - `validate_handle(name)` helper
  - `wrap_output(handle, op)` helper

**Impact:**
- Removed ~15 lines of boilerplate per layer class
- Consolidated FFI handle management across 13+ neural network layer classes
- Consistent error messaging

### 6.3 MethodRegistry Created (Rust)

**Files created:**
- `src/compiler/src/method_registry/mod.rs`
- `src/compiler/src/method_registry/registry.rs`
- `src/compiler/src/method_registry/builtins.rs`

**Features:**
- `MethodRegistry` - Centralized registry for built-in methods
- `MethodInfo` - Method metadata (name, runtime_fn, param_count, is_mutating)
- `RuntimeFn` - Runtime function specification (Simple/WithSignature/Inline)
- Static arrays for Array, Dict, String, Tuple, Option, Int, Float methods
- `GLOBAL_REGISTRY` - LazyLock-initialized global registry

**Methods registered:**
- Array: 17 methods (len, push, pop, get, set, clear, contains, slice, first, last, etc.)
- Dict: 10 methods (len, get, set, clear, keys, values, contains, remove, etc.)
- String: 13 methods (len, concat, contains, slice, starts_with, ends_with, trim, etc.)
- Tuple: 3 methods (len, get, set)
- Option: 7 methods (is_some, is_none, unwrap, unwrap_or, expect, map, and_then)
- Int: 5 methods (abs, to_string, to_float, clamp, pow)
- Float: 16 methods (abs, floor, ceil, round, to_string, to_int, sqrt, trig, etc.)

**Tests:** 10 unit tests all passing

### 6.4 Iterable Defaults Created (Simple)

**File created:**
- `simple/std_lib/src/core/iterable_defaults.spl`

**Default implementations provided:**
- Predicate methods: `all_impl`, `any_impl`, `find_impl`, `find_index_impl`, `count_matching_impl`
- Reduction methods: `fold_impl`, `reduce_impl`, `sum_impl`, `product_impl`
- Extrema methods: `max_impl`, `min_impl`
- First/Last: `first_impl`, `last_impl`
- Collection building: `filter_impl`, `map_impl`, `flat_map_impl`
- Partitioning: `partition_impl`, `take_impl`, `drop_impl`, `take_while_impl`, `drop_while_impl`
- Combine: `zip_impl`, `enumerate_impl`
- Grouping: `group_by_impl`, `chunk_impl`

**Usage:**
Collections can delegate to these implementations:
```simple
impl Sequence<T> for MyCollection<T>:
    fn all(predicate: fn(&T) -> bool) -> bool:
        iterable_defaults::all_impl(self, predicate)
```

**Impact:**
- 20+ reusable iteration functions
- Any new collection type can use these defaults
- Eliminates need to duplicate iteration logic

### 6.5 Bug Fixes Applied

| File | Fix |
|------|-----|
| `codegen/instr/calls.rs` | Changed `FunctionRef` to `CallTarget` |
| `mir/lower/tests/contract_modes.rs` | Added `ContractMode` import |
| `cli/commands/misc_commands.rs` | Fixed `DiagramGenOptions` type |
| `todo_db.rs` | Fixed `SdnValue::int()` call, partial move fix |
| `cli/commands/startup.rs` | Fixed `total_time()` test |
| `examples/i18n_error_example.rs` | Fixed `to_diagnostic()` call |
| `doctest/parser.rs` | Fixed test expectations |
| `doctest/markdown.rs` | Fixed indented fence parsing, test expectations |
| `doctest/discovery.rs` | Fixed test expectations |

---

## Appendix: File Locations Summary

### Critical Duplication Files
```
src/compiler/src/interpreter/expr/ops.rs      # Binary/Unary ops
src/compiler/src/codegen/instr/core.rs        # Codegen ops
src/compiler/src/interpreter_method/          # Method dispatch (1000+ lines)
src/compiler/src/codegen/instr/methods.rs     # Codegen methods
src/compiler/src/value_impl.rs                # Type coercion
```

### Migration Candidate Files
```
src/driver/src/todo_parser.rs                 # 608 lines → Simple
src/common/src/config_env.rs                  # 423 lines → Simple
src/driver/src/cli/test_output.rs             # 410 lines → Simple
src/driver/src/cli/migrate/generics.rs        # 200 lines → Simple
src/driver/src/cli/help.rs                    # 188 lines → Simple
```

### Simple Duplication Files
```
simple/std_lib/src/ml/torch/nn/               # 500+ lines duplicated
simple/std_lib/src/graphics/math/vector.spl   # 200+ lines duplicated
simple/std_lib/src/core/array.spl             # 150+ lines duplicated
simple/std_lib/src/core/primitives.spl        # 100+ lines duplicated
```
