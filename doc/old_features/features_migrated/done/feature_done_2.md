# Completed Features (Archive 2)

This document archives completed features from December 2025 (second batch).

---

## Completed Codegen Features (#99-#103)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #99 | Body Block Outlining | 4 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`public_api_coverage_tests.rs:test_codegen_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #100 | Capture Buffer & VReg Remapping | 4 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`public_api_coverage_tests.rs:test_codegen_*`](../tests/system/public_api_coverage_tests.rs) | `src/compiler/tests/` |
| #101 | Generator State Machine Codegen | 5 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/compiler/tests/` |
| #102 | Future Body Execution | 4 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/compiler/tests/` |
| #103 | Codegen Parity Completion | 5 | ✅ | R | [codegen_technical.md](codegen_technical.md) | [`execution_tests.rs`](../tests/system/execution_tests.rs) | `src/compiler/tests/` |

### Feature #102 - Future Body Execution

**Implementation:**
- Future bodies are generated as outlined functions via body outlining infrastructure
- Capture buffers properly marshal live-in variables into runtime arrays
- `MirInst::FutureCreate` generates function pointers to outlined bodies
- Runtime FFI `rt_future_new` eagerly executes future bodies with captured context
- `rt_future_await` returns stored results (futures ready immediately after creation)

**Test Coverage:**
- `runner_future_basic`, `runner_future_with_computation`
- `runner_future_multiple`, `runner_future_function_call`
- `runner_async_fn_basic`, `runner_async_can_call_async`
- `parity_future_*` tests (4 tests)

### Feature #103 - Codegen Parity Completion

**Implementation:**
- Hybrid execution infrastructure in `src/compiler/src/mir/hybrid.rs`
- `apply_hybrid_transform()` converts calls to non-compilable functions into `InterpCall`
- Compilability analysis in `src/compiler/src/compilability.rs` (20+ fallback reasons)
- `MirInst::InterpCall` and `MirInst::InterpEval` for interpreter fallback
- Runtime FFI handlers `rt_interp_call` and `rt_interp_eval`
- Interpreter bridge in `src/compiler/src/interpreter_ffi.rs`

**Test Coverage (22 parity tests):**
- Generator tests: `parity_generator_*` (8 tests)
- Future tests: `parity_future_*` (4 tests)
- Core tests: `parity_control_flow_nested`, `parity_recursive_function`
- Data structure tests: `parity_struct_field_access`, `parity_enum_pattern_match`
- Collection tests: `parity_array_operations`, `parity_tuple_destructure`, `parity_dictionary_access`
- Function tests: `parity_function_composition`, `parity_early_return`, `parity_boolean_logic`
- Actor test: `parity_actor_basic_spawn`

---

## Completed Concurrency Features (#110-#157)

### Channels (#110-#116)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #110 | `rt_channel_new` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`feature_tests_advanced.rs:test_feature_84_channel_*`](../tests/system/feature_tests_advanced.rs) | `src/runtime/tests/` |
| #111 | `rt_channel_send` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`feature_tests_advanced.rs:test_feature_84_channel_*`](../tests/system/feature_tests_advanced.rs) | `src/runtime/tests/` |
| #112 | `rt_channel_recv` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`feature_tests_advanced.rs:test_feature_84_channel_*`](../tests/system/feature_tests_advanced.rs) | `src/runtime/tests/` |
| #113 | `rt_channel_try_recv` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`feature_tests_advanced.rs:test_feature_84_channel_try_recv`](../tests/system/feature_tests_advanced.rs) | `src/runtime/tests/` |
| #114 | `rt_channel_recv_timeout` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_actor_handle_recv_timeout`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #115 | `rt_channel_close` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #116 | `rt_channel_is_closed` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |

### Generators (#120-#126)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #120 | `rt_generator_new` | 4 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #121 | `rt_generator_next` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #122 | `rt_generator_get_state` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`struct_coverage_tests.rs`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #123 | `rt_generator_set_state` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`struct_coverage_tests.rs`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #124 | `rt_generator_store_slot` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`struct_coverage_tests.rs`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #125 | `rt_generator_load_slot` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`struct_coverage_tests.rs`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |
| #126 | `rt_generator_mark_done` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`struct_coverage_tests.rs`](../tests/system/struct_coverage_tests.rs) | `src/runtime/tests/` |

### Executor (#130-#134)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #130 | `rt_executor_set_mode` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #131 | `rt_executor_start` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #132 | `rt_executor_poll` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #133 | `rt_executor_poll_all` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #134 | `rt_executor_shutdown` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |

### Actor Runtime (#140-#145)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #140 | `rt_actor_spawn` | 4 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_spawn_actor`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #141 | `rt_actor_send` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_send_to`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #142 | `rt_actor_recv` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_actor_handle_*`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #143 | `rt_actor_join` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_actor_handle_*`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #144 | `rt_actor_id` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs:test_actor_handle_id`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |
| #145 | `rt_actor_is_alive` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`coverage_tests.rs`](../tests/system/coverage_tests.rs) | `src/runtime/tests/` |

### Future Runtime (#150-#157)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #150 | `rt_future_new` | 4 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #151 | `rt_future_await` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #152 | `rt_future_is_ready` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #153 | `rt_future_get_result` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #154 | `rt_future_all` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #155 | `rt_future_race` | 3 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #156 | `rt_future_resolve` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |
| #157 | `rt_future_reject` | 2 | ✅ | R | [spec/concurrency.md](spec/concurrency.md) | [`runner_tests.rs`](../tests/system/runner_tests.rs) | `src/runtime/tests/` |

---

## Completed Pattern Matching (#160-#172)

All 79 BDD tests passing.

| Feature ID | Pattern Type | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|--------------|------------|--------|------|-----|--------|--------|
| #160 | Integer/boolean/string literals | 2 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_pattern_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #161 | Variable binding (`n =>`) | 2 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_pattern_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #162 | Wildcard (`_ =>`) | 1 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_pattern_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #163 | Unit enum variants | 2 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_enums_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #164 | Single-payload enum variants | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_enums_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #165 | Multi-payload enum variants | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_enums_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #166 | Tuple destructuring | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_pattern_matching_destructure`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #167 | Struct destructuring | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_structs_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #168 | Guard clauses (`if` guards) | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_advanced.rs:test_feature_74_match_guard_*`](../tests/system/feature_tests_advanced.rs) | `src/compiler/tests/` |
| #169 | Or patterns (`1 \| 2 \| 3`) | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_advanced.rs:test_feature_80_or_pattern`](../tests/system/feature_tests_advanced.rs) | `src/compiler/tests/` |
| #170 | Range patterns (`1..=10`) | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_advanced.rs:test_feature_81_range_pattern_*`](../tests/system/feature_tests_advanced.rs) | `src/compiler/tests/` |
| #171 | Array patterns (`[a, b]`) | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_basic.rs:test_feature_array_*`](../tests/system/feature_tests_basic.rs) | `src/compiler/tests/` |
| #172 | `if-let` patterns | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`feature_tests_advanced.rs:test_feature_75_if_let_*`](../tests/system/feature_tests_advanced.rs) | `src/compiler/tests/` |

**Test File:** `simple/std_lib/test/unit/core/pattern_matching_spec.spl`

---

## Completed Testing Features (#189-#241)

### BDD Extensions (#189-#191)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #189 | `shared_examples` | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #190 | `it_behaves_like` | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #191 | `let` memoization | 2 | ✅ | S | [spec/testing/testing_bdd_framework.md](spec/testing/testing_bdd_framework.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |

### Mock Library (#230-#241)

Fluent mock API for unit tests (stub methods, verify calls, argument matchers).

**Extended by:** AOP Mocking (#1020-1025) - adds trait-boundary mocking via DI predicates (`mock Name implements Trait:` syntax)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #230 | `mock <Type>` | 3 | ✅ | S+R | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | `src/compiler/tests/` |
| #231 | `spy <Type>` | 3 | ✅ | S+R | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | `src/compiler/tests/` |
| #232 | `.when(:method)` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #233 | `.withArgs(args)` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #234 | `.returns(value)` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #235 | `.returnsOnce(value)` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #236 | `.verify(:method)` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #237 | `.called()` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #238 | `.calledTimes(n)` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #239 | `.calledWith(args)` | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/spec_framework_spec.spl`](../simple/std_lib/test/system/spec/spec_framework_spec.spl) | - |
| #240 | `any()` matcher | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/matchers/spec_matchers_spec.spl`](../simple/std_lib/test/system/spec/matchers/spec_matchers_spec.spl) | - |
| #241 | `gt(x)`, `lt(x)`, etc | 2 | ✅ | S | [test.md](test.md) | [`std_lib/test/system/spec/matchers/spec_matchers_spec.spl`](../simple/std_lib/test/system/spec/matchers/spec_matchers_spec.spl) | - |

---

## Completed CLI Features (#250-#258)

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #250 | `simple test` command | 2 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #251 | `--unit` flag | 1 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #252 | `--integration` flag | 1 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #253 | `--system` flag | 1 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #254 | `--tag <name>` | 2 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #255 | `--fail-fast` | 1 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #256 | `--seed N` | 1 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #257 | `--format json` | 2 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |
| #258 | `--format doc` | 2 | ✅ | R | [system_test.md](system_test.md) | [`cli_tests.rs`](../tests/system/cli_tests.rs) | `src/driver/tests/` |

### Output Format Details (CLI-008, CLI-009)

**JSON Format (`--format json` or `--json`):**
```json
{
  "success": true,
  "total_passed": 5,
  "total_failed": 0,
  "total_duration_ms": 150,
  "files": [
    {
      "path": "test/unit/foo_spec.spl",
      "passed": 3,
      "failed": 0,
      "duration_ms": 100,
      "error": null
    }
  ]
}
```

**Doc Format (`--format doc` or `--doc`):**
```
test/unit
  ✓ foo_spec.spl (100ms)
  ✓ bar_spec.spl (50ms)

test/system
  ✓ system_spec.spl (80ms)

─────────────────────────────────────────────────────────────────
5 examples, 0 failures (230ms)
```

**Implementation Files:**
- `src/driver/src/cli/test_runner.rs` - OutputFormat enum, formatters
- `src/driver/src/main.rs` - CLI argument parsing
- `src/driver/tests/test_runner_tests.rs` - Unit tests

---

## Completed Contract Features (#400-#403)

### Core Contract Blocks

| Feature ID | Feature | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|------------|--------|------|-----|--------|--------|
| #400 | `in:` preconditions | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `src/compiler/tests/` |
| #401 | `out(ret):` postconditions | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `src/compiler/tests/` |
| #402 | `out_err(err):` | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `src/compiler/tests/` |
| #403 | `invariant:` routine | 3 | ✅ | R | [spec/functions.md](spec/functions.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `src/compiler/tests/` |

---

## Completed Formal Verification (#960-#964)

### Contract Verification

| Feature ID | Description | Difficulty | Status | Impl | Doc | S-Test | R-Test |
|------------|-------------|------------|--------|------|-----|--------|--------|
| #960 | Precondition semantics (`in:`) | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `verification/type_inference_compile/` |
| #961 | Postcondition semantics (`out(ret):`) | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `verification/type_inference_compile/` |
| #962 | Error postcondition semantics (`out_err(err):`) | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `verification/type_inference_compile/` |
| #963 | Routine invariant preservation | 5 | ✅ | R | [formal_verification.md](formal_verification.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `verification/type_inference_compile/` |
| #964 | `old(expr)` snapshot correctness | 4 | ✅ | R | [formal_verification.md](formal_verification.md) | [`core_tests.rs`](../tests/system/core_tests.rs) | `verification/type_inference_compile/` |

**Lean 4 Model:** `verification/type_inference_compile/src/Contracts.lean`

---

## Importance Scale

- **High**: Core functionality, blocks other features, or critical for usability
- **Medium**: Important but not blocking, enhances developer experience
- **Low**: Nice-to-have, convenience features, edge cases

## Difficulty Scale

- **1**: Trivial (< 1 hour, simple change)
- **2**: Easy (1-4 hours, straightforward)
- **3**: Medium (1-2 days, some complexity)
- **4**: Hard (3-5 days, significant work)
- **5**: Very Hard (1+ weeks, major effort)
