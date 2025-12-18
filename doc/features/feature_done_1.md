# Completed Features (Archive 1)

This document archives all completed features as of December 2025.

---

## Completed Infrastructure Components (#1-#8)

| Feature ID | Component | Status | Impl | Doc | S-Test | R-Test |
|------------|-----------|--------|------|-----|--------|--------|
| #1 | **Lexer** | ✅ | R | [spec/lexer_parser.md](spec/lexer_parser.md) | [`public_api_coverage_tests.rs:test_lexer_*`](../tests/system/public_api_coverage_tests.rs) | `src/parser/tests/` |
| #2 | **Parser** | ✅ | R | [spec/lexer_parser.md](spec/lexer_parser.md) | [`public_api_coverage_tests.rs:test_parser_*`](../tests/system/public_api_coverage_tests.rs) | `src/parser/tests/` |
| #3 | **AST** | ✅ | R | [spec/lexer_parser.md](spec/lexer_parser.md) | [`public_api_coverage_tests.rs`](../tests/system/public_api_coverage_tests.rs) | `src/parser/tests/` |
| #4 | **HIR** | ✅ | R | [architecture.md](architecture.md) | [`public_api_coverage_tests.rs:test_hir_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #5 | **MIR** | ✅ | R | [codegen_status.md](codegen_status.md) | [`public_api_coverage_tests.rs:test_mir_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #6 | **RuntimeValue** | ✅ | R | [spec/stdlib.md](spec/stdlib.md) | [`struct_coverage_tests.rs`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #7 | **GC** | ✅ | R | [spec/memory.md](spec/memory.md) | [`struct_coverage_tests.rs:test_gc_*`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #8 | **Package Manager** | ✅ | R | [spec/stdlib.md](spec/stdlib.md) | [`pkg_tests.rs`](../tests/system/pkg_tests.rs) | `src/pkg/tests/` |

---

## Completed Core Language Features (#10-#24)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #10 | Basic Types (i8-i64, u8-u64, f32-f64, bool, str, nil) | ✅ | R | [spec/types.md](spec/types.md) | [`feature_tests_basic.rs:test_feature_basic_types_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #11 | Variables | ✅ | R | [spec/syntax.md](spec/syntax.md) | [`feature_tests_basic.rs:test_feature_variables_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #12 | Functions | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_functions_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #13 | Control Flow | ✅ | R | [spec/syntax.md](spec/syntax.md) | [`feature_tests_basic.rs:test_feature_control_flow_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #14 | Structs | ✅ | R | [spec/data_structures.md](spec/data_structures.md) | [`feature_tests_basic.rs:test_feature_structs_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #15 | Classes | ✅ | R | [spec/data_structures.md](spec/data_structures.md) | [`feature_tests_basic.rs:test_feature_classes_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #16 | Enums | ✅ | R | [spec/data_structures.md](spec/data_structures.md) | [`feature_tests_basic.rs:test_feature_enums_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #17 | Pattern Matching | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_pattern_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #18 | GC Memory Management | ✅ | R | [spec/memory.md](spec/memory.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `src/runtime/tests/` |
| #19 | Borrowing | ✅ | R | [spec/memory.md](spec/memory.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `src/compiler/tests/` |
| #20 | Actors | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_actor_*`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #21 | Async/Await | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #22 | Generators | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #23 | Futures | ✅ | S+R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #24 | Closures, Macros, String Interpolation | ✅ | R | [spec/metaprogramming.md](spec/metaprogramming.md) | [`feature_tests_basic.rs:test_feature_lambdas_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |

---

## Completed Codegen Features (#95-#98)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #95 | Capture Buffer & VReg Remapping | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`public_api_coverage_tests.rs:test_codegen_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #96 | Generator State Machine Codegen | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/compiler/tests/` |
| #97 | LLVM Backend | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`execution_tests.rs`](../tests/system/execution_tests.rs) | `src/compiler/llvm_tests/` |

---

## Completed Testing Features (#180-#197)

### BDD Spec Framework (#180-#188)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #180 | `describe` blocks | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #181 | `context` blocks | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #182 | `it` examples | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #183 | `before_each` hook | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #184 | `after_each` hook | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #185 | `before_all` hook | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #186 | `after_all` hook | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #187 | `expect ... to` matcher | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/matchers/spec_matchers_spec.spl`](../simple/std_lib/test/system/spec/matchers/spec_matchers_spec.spl) | - |
| #188 | `expect_raises` | ✅ | S | [spec/bdd_spec.md](spec/bdd_spec.md) | [`std_lib/test/system/spec/matchers/spec_matchers_spec.spl`](../simple/std_lib/test/system/spec/matchers/spec_matchers_spec.spl) | - |

### Doctest (#192-#197)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #192 | `>>>` prompt | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/parser/parser_spec.spl`](../simple/std_lib/test/system/doctest/parser/parser_spec.spl) | `src/driver/tests/` |
| #193 | Expected output | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/matcher/matcher_spec.spl`](../simple/std_lib/test/system/doctest/matcher/matcher_spec.spl) | `src/driver/tests/` |
| #194 | `...` continuation | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/parser/parser_spec.spl`](../simple/std_lib/test/system/doctest/parser/parser_spec.spl) | `src/driver/tests/` |
| #195 | `# doctest: +SKIP` | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/doctest_advanced_spec.spl`](../simple/std_lib/test/system/doctest/doctest_advanced_spec.spl) | `src/driver/tests/` |
| #196 | `# doctest: +ELLIPSIS` | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/system/doctest/doctest_advanced_spec.spl`](../simple/std_lib/test/system/doctest/doctest_advanced_spec.spl) | `src/driver/tests/` |
| #197 | FFI integration | ✅ | R | [system_test.md](system_test.md) | [`std_lib/test/integration/doctest/discovery_spec.spl`](../simple/std_lib/test/integration/doctest/discovery_spec.spl) | `src/driver/tests/` |

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

| Feature ID | Project | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #950 | `type_inference_compile` | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_type_registry_*`](../tests/system/public_api_coverage_tests.rs) | `verification/type_inference_compile/` |
| #951 | `type_inference_compile/Generics` | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_type_registry_*`](../tests/system/public_api_coverage_tests.rs) | `verification/type_inference_compile/` |

**Generics Model Details (FV-002):**
- Type variables (`Ty.var`)
- Generic types: `generic0`, `generic1`, `generic2` (up to 2 type params)
- Type schemes (`∀vars. ty`) for let-polymorphism
- Substitution with composition
- Unification with occurs check
- Instantiate/Generalize for let-bindings

### Memory Safety Verification (#952-#954)

| Feature ID | Project | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #952 | `manual_pointer_borrow` | ✅ | R | [formal_verification.md](formal_verification.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `verification/manual_pointer_borrow/` |
| #953 | `gc_manual_borrow` | ✅ | R | [formal_verification.md](formal_verification.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `verification/gc_manual_borrow/` |
| #954 | `nogc_compile` | ✅ | R | [formal_verification.md](formal_verification.md) | [`memory_tests.rs`](../tests/system/memory_tests.rs) | `verification/nogc_compile/` |

### Effect System Verification (#955)

| Feature ID | Project | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #955 | `async_compile` | ✅ | R | [formal_verification.md](formal_verification.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `verification/async_compile/` |

### Module System Verification (#956-#958)

| Feature ID | Project | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #956 | `module_resolution` | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_module_*`](../tests/system/public_api_coverage_tests.rs) | `verification/module_resolution/` |
| #957 | `visibility_export` | ✅ | R | [formal_verification.md](formal_verification.md) | [`public_api_coverage_tests.rs:test_module_*`](../tests/system/public_api_coverage_tests.rs) | `verification/visibility_export/` |
| #958 | `macro_auto_import` | ✅ | R | [formal_verification.md](formal_verification.md) | [`integration_tests.rs`](../tests/system/integration_tests.rs) | `verification/macro_auto_import/` |

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
