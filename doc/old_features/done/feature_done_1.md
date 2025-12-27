# Completed Features (Archive 1)

This document archives all completed features as of December 2025.

---

## Completed Infrastructure Components (#1-#9)

| Feature ID | Component | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|-----------|------------|--------|------|-----|--------|--------|
| #1 | **Lexer** | 3 | ✅ | R | [spec/lexer_parser.md](spec/lexer_parser.md) | [`public_api_coverage_tests.rs:test_lexer_*`](../tests/system/public_api_coverage_tests.rs) | `src/parser/tests/` |
| #2 | **Parser** | 4 | ✅ | R | [spec/lexer_parser.md](spec/lexer_parser.md) | [`public_api_coverage_tests.rs:test_parser_*`](../tests/system/public_api_coverage_tests.rs) | `src/parser/tests/` |
| #3 | **AST** | 3 | ✅ | R | [spec/lexer_parser.md](spec/lexer_parser.md) | [`public_api_coverage_tests.rs`](../tests/system/public_api_coverage_tests.rs) | `src/parser/tests/` |
| #4 | **HIR** | 4 | ✅ | R | [architecture.md](architecture.md) | [`public_api_coverage_tests.rs:test_hir_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #5 | **MIR** | 4 | ✅ | R | [codegen_status.md](codegen_status.md) | [`public_api_coverage_tests.rs:test_mir_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #6 | **RuntimeValue** | 4 | ✅ | R | [spec/stdlib.md](spec/stdlib.md) | [`struct_coverage_tests.rs`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #7 | **GC** | 5 | ✅ | R | [spec/memory.md](spec/memory.md) | [`struct_coverage_tests.rs:test_gc_*`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #8 | **Package Manager** | 4 | ✅ | R | [spec/stdlib.md](spec/stdlib.md) | [`pkg_tests.rs`](../tests/system/pkg_tests.rs) | `src/pkg/tests/` |
| #9 | **SMF (Simple Module Format)** | 4 | ✅ | R | [architecture.md](architecture.md) | - | `src/compiler/src/linker/smf_writer.rs`, `src/loader/` |

### Feature #9 - SMF (Simple Module Format)

SMF is the binary format for compiled Simple programs. It enables:
- **Compilation**: `simple compile src.spl -o out.smf` generates portable binary modules
- **Execution**: `simple out.smf` runs compiled binaries directly
- **Cross-compilation**: `simple compile src.spl --target aarch64` for different architectures

**Implementation:**
- `SmfWriter` in `src/compiler/src/linker/smf_writer.rs` - Writes SMF files from compiled code
- `ModuleLoader` in `src/loader/` - Loads and executes SMF binaries
- Supports code sections, data sections (mutable/readonly), symbol tables, and relocations
- Magic: `SMF\0`, versioned format with section headers

---

## Completed Core Language Features (#10-#24)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #10 | Basic Types (i8-i64, u8-u64, f32-f64, bool, str, nil) | 2 | ✅ | R | [spec/types.md](spec/types.md) | [`feature_tests_basic.rs:test_feature_basic_types_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #11 | Variables | 2 | ✅ | R | [spec/syntax.md](spec/syntax.md) | [`feature_tests_basic.rs:test_feature_variables_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #12 | Functions | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_functions_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #13 | Control Flow | 2 | ✅ | R | [spec/syntax.md](spec/syntax.md) | [`feature_tests_basic.rs:test_feature_control_flow_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #14 | Structs | 3 | ✅ | R | [spec/data_structures.md](spec/data_structures.md) | [`feature_tests_basic.rs:test_feature_structs_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #15 | Classes | 3 | ✅ | R | [spec/data_structures.md](spec/data_structures.md) | [`feature_tests_basic.rs:test_feature_classes_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #16 | Enums | 3 | ✅ | R | [spec/data_structures.md](spec/data_structures.md) | [`feature_tests_basic.rs:test_feature_enums_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #17 | Pattern Matching | 4 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_pattern_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #18 | GC Memory Management | 5 | ✅ | R | [spec/memory.md](spec/memory.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `src/runtime/tests/` |
| #19 | Borrowing | 4 | ✅ | R | [spec/memory.md](spec/memory.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `src/compiler/tests/` |
| #20 | Actors | 4 | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_actor_*`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #21 | Async/Await | 4 | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #22 | Generators | 4 | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #23 | Futures | 4 | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #24 | Closures, Macros, String Interpolation | 3 | ✅ | R | [spec/metaprogramming.md](spec/metaprogramming.md) | [`feature_tests_basic.rs:test_feature_lambdas_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |

---

## Completed Codegen Features (#95-#98)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #95 | Capture Buffer & VReg Remapping | 4 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`public_api_coverage_tests.rs:test_codegen_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #96 | Generator State Machine Codegen | 5 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/compiler/tests/` |
| #97 | LLVM Backend | 5 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`execution_tests.rs`](../tests/system/execution_tests.rs) | `src/compiler/llvm_tests/` |

---

## Completed Testing Features (#180-#197)

### BDD Spec Framework (#180-#188)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #180 | `describe` blocks | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #181 | `context` blocks | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #182 | `it` examples | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #183 | `before_each` hook | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #184 | `after_each` hook | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #185 | `before_all` hook | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #186 | `after_all` hook | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #187 | `expect ... to` matcher | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/matchers/spec_matchers_spec.spl`](../simple/std_lib/test/system/spec/matchers/spec_matchers_spec.spl) | - |
| #188 | `expect_raises` | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/matchers/spec_matchers_spec.spl`](../simple/std_lib/test/system/spec/matchers/spec_matchers_spec.spl) | - |

### Doctest (#192-#197)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #192 | `>>>` prompt | 3 | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/parser/parser_spec.spl`](../simple/std_lib/test/system/doctest/parser/parser_spec.spl) | `src/driver/tests/` |
| #193 | Expected output | 2 | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/matcher/matcher_spec.spl`](../simple/std_lib/test/system/doctest/matcher/matcher_spec.spl) | `src/driver/tests/` |
| #194 | `...` continuation | 2 | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/parser/parser_spec.spl`](../simple/std_lib/test/system/doctest/parser/parser_spec.spl) | `src/driver/tests/` |
| #195 | `# doctest: +SKIP` | 2 | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/doctest_advanced_spec.spl`](../simple/std_lib/test/system/doctest/doctest_advanced_spec.spl) | `src/driver/tests/` |
| #196 | `# doctest: +ELLIPSIS` | 2 | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/doctest_advanced_spec.spl`](../simple/std_lib/test/system/doctest/doctest_advanced_spec.spl) | `src/driver/tests/` |
| #197 | FFI integration | 3 | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/integration/doctest/discovery_spec.spl`](../simple/std_lib/test/integration/doctest/discovery_spec.spl) | `src/driver/tests/` |

### Doctest Example

```simple
/// Adds two numbers.
///
/// >>> add(1, 2)
/// 3
///
/// >>> add(-1, 1)
/// 0
fn add(a: i64, b: i64) -> i64:
    return a + b
```

---

## Completed Formal Verification Features (#950-#970)

Located in `verification/` directory, each project is a Lean 4 proof system.

### Type System Verification (#950-#951)

| Feature ID | Project | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #950 | `type_inference_compile` | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_type_registry_*`](../tests/system/public_api_coverage_tests.rs) | `verification/type_inference_compile/` |
| #951 | `type_inference_compile/Generics` | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_type_registry_*`](../tests/system/public_api_coverage_tests.rs) | `verification/type_inference_compile/` |

**Generics Model Details (FV-002):**
- Type variables (`Ty.var`)
- Generic types: `generic0`, `generic1`, `generic2` (up to 2 type params)
- Type schemes (`∀vars. ty`) for let-polymorphism
- Substitution with composition
- Unification with occurs check
- Instantiate/Generalize for let-bindings

### Memory Safety Verification (#952-#954)

| Feature ID | Project | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #952 | `manual_pointer_borrow` | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `verification/manual_pointer_borrow/` |
| #953 | `gc_manual_borrow` | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `verification/gc_manual_borrow/` |
| #954 | `nogc_compile` | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `verification/nogc_compile/` |

### Effect System Verification (#955)

| Feature ID | Project | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #955 | `async_compile` | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `verification/async_compile/` |

### Module System Verification (#956-#958)

| Feature ID | Project | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #956 | `module_resolution` | 4 | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_module_*`](../tests/system/public_api_coverage_tests.rs) | `verification/module_resolution/` |
| #957 | `visibility_export` | 4 | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_module_*`](../tests/system/public_api_coverage_tests.rs) | `verification/visibility_export/` |
| #958 | `macro_auto_import` | 4 | ✅ | R | [formal_verification.md](formal_verification.md) | [`integration_tests.rs`](../tests/system/integration_tests.rs) | `verification/macro_auto_import/` |

### Integration with Rust Implementation

The Rust type system in `src/type/` mirrors the Lean models:

| Lean Type | Rust Type | Location |
|-----------|-----------|----------|
| `Ty` | `Type` | `src/type/src/lib.rs` |
| `Scheme` | `TypeScheme` | `src/type/src/lib.rs` |
| `Subst` | `Substitution` | `src/type/src/lib.rs` |
| `unify` | `TypeChecker::unify` | `src/type/src/checker_unify.rs` |
| `instantiate` | `TypeChecker::instantiate` | `src/type/src/checker_builtins.rs` |
| `generalize` | `TypeChecker::generalize` | `src/type/src/checker_builtins.rs` |

### Building Verification Projects

```bash
cd verification/<project>
lake build
```

All projects use Lean 4 v4.26.0 (managed via `.elan`).

### Proven Theorems

- `infer_deterministic` - Type inference returns unique type
- `emptySubst_identity` - Empty substitution is identity
- `applySubst_*` - Substitution preserves primitives
- `occurs_*` - Occurs check properties

### Partial Proofs (with `sorry`)

- `unify_sound` - Unification produces correct substitution

---

## Completion Timeline (December 2025)

- ✅ LLVM Backend (32-bit + 64-bit, 43 tests)
- ✅ Generator State Machine Codegen
- ✅ Capture Buffer & VReg Remapping
- ✅ BDD Spec Framework Sprint 1
- ✅ Doctest Sprint 2
- ✅ JJ Integration (8/12 tasks - 67%)
- ✅ Generic Type Inference Model (Lean 4)
