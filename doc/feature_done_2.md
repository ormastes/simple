# Completed Features (Archive 2)

This document archives completed features from December 2025 (second batch).

---

## Completed Codegen Features

| Feature ID | Feature | Importance | Difficulty | Description |
|------------|---------|------------|------------|-------------|
| #99 | Body Block Outlining | High | 4 | `shared.rs::expand_with_outlined` |
| #100 | Capture Buffer & VReg Remapping | High | 4 | Closure capture handling |
| #101 | Generator State Machine Codegen | High | 5 | Full generator lowering |
| #102 | Future Body Execution | High | 4 | Eager execution with body outlining |
| #103 | Codegen Parity Completion | High | 5 | Hybrid execution with InterpCall fallback |

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

## Completed Concurrency Features

### Channels (Complete)

| Feature | Importance | Difficulty | Description |
|---------|------------|------------|-------------|
| `rt_channel_new` | High | 2 | Create new channel |
| `rt_channel_send` | High | 2 | Send value through channel |
| `rt_channel_recv` | High | 3 | Blocking receive with timeout |
| `rt_channel_try_recv` | Medium | 2 | Non-blocking receive |
| `rt_channel_recv_timeout` | Medium | 2 | Receive with custom timeout |
| `rt_channel_close` | Medium | 1 | Close channel |
| `rt_channel_is_closed` | Low | 1 | Check if channel is closed |

### Generators (Complete)

| Feature | Importance | Difficulty | Description |
|---------|------------|------------|-------------|
| `rt_generator_new` | High | 3 | Create generator with slots |
| `rt_generator_next` | High | 3 | Resume generator |
| `rt_generator_get_state` | Medium | 2 | Get state machine position |
| `rt_generator_set_state` | Medium | 2 | Set state machine position |
| `rt_generator_store_slot` | Medium | 2 | Store local variable |
| `rt_generator_load_slot` | Medium | 2 | Load local variable |
| `rt_generator_mark_done` | Medium | 1 | Mark generator as exhausted |

### Executor (Complete)

| Feature | Importance | Difficulty | Description |
|---------|------------|------------|-------------|
| `rt_executor_set_mode` | High | 2 | Set Threaded (0) or Manual (1) mode |
| `rt_executor_start` | High | 3 | Start executor (spawn workers) |
| `rt_executor_poll` | Medium | 2 | Poll one task (manual mode) |
| `rt_executor_poll_all` | Medium | 2 | Poll all tasks (manual mode) |
| `rt_executor_shutdown` | Medium | 2 | Shutdown executor |

### Actor Runtime (Partial)

| Feature | Importance | Difficulty | Description |
|---------|------------|------------|-------------|
| `rt_actor_spawn` | High | 3 | Spawn actor with body function |
| `rt_actor_send` | High | 2 | Send message to actor |
| `rt_actor_recv` | High | 3 | Receive message from inbox |
| `rt_actor_join` | Medium | 2 | Wait for actor to complete |
| `rt_actor_id` | Low | 1 | Get actor ID |
| `rt_actor_is_alive` | Low | 1 | Check if actor is running |

### Future Runtime (Partial)

| Feature | Importance | Difficulty | Description |
|---------|------------|------------|-------------|
| `rt_future_new` | High | 3 | Create future with body (eager) |
| `rt_future_await` | High | 3 | Await future result |
| `rt_future_is_ready` | Medium | 1 | Check if future is ready |
| `rt_future_get_result` | Medium | 2 | Get result without blocking |
| `rt_future_all` | Medium | 2 | Wait for all futures |
| `rt_future_race` | Medium | 2 | Wait for first future |
| `rt_future_resolve` | Low | 1 | Create resolved future |
| `rt_future_reject` | Low | 1 | Create rejected future |

---

## Completed Pattern Matching

All 79 BDD tests passing.

| Pattern Type | Importance | Difficulty | Status |
|--------------|------------|------------|--------|
| Integer/boolean/string literals | High | 2 | ✅ |
| Variable binding (`n =>`) | High | 2 | ✅ |
| Wildcard (`_ =>`) | High | 1 | ✅ |
| Unit enum variants | High | 2 | ✅ |
| Single-payload enum variants | High | 3 | ✅ |
| Multi-payload enum variants | High | 3 | ✅ |
| Tuple destructuring | High | 3 | ✅ |
| Struct destructuring | Medium | 3 | ✅ |
| Guard clauses (`if` guards) | Medium | 3 | ✅ |
| Or patterns (`1 \| 2 \| 3`) | Medium | 3 | ✅ |
| Range patterns (`1..=10`) | Medium | 3 | ✅ |
| Array patterns (`[a, b]`) | Medium | 3 | ✅ |
| `if-let` patterns | Medium | 2 | ✅ |

**Test File:** `simple/std_lib/test/unit/core/pattern_matching_spec.spl`

---

## Completed Testing Features

### BDD Extensions

| Feature ID | Feature | Importance | Difficulty | Description |
|------------|---------|------------|------------|-------------|
| TEST-010 | `shared_examples` | Medium | 3 | Reusable example groups |
| TEST-011 | `it_behaves_like` | Medium | 2 | Include shared examples |
| TEST-012 | `let` memoization | Medium | 3 | Memoized per-example state |

### Mock Library (Complete)

| Feature ID | Feature | Importance | Difficulty | Description |
|------------|---------|------------|------------|-------------|
| MOCK-001 | `mock <Type>` | High | 4 | Create mock implementing interface |
| MOCK-002 | `spy <Type>` | Medium | 3 | Create spy wrapping real object |
| MOCK-003 | `.when(:method)` | High | 3 | Configure method behavior |
| MOCK-004 | `.withArgs(args)` | High | 2 | Match specific arguments |
| MOCK-005 | `.returns(value)` | High | 2 | Set return value |
| MOCK-006 | `.returnsOnce(value)` | Medium | 2 | Return value once |
| MOCK-007 | `.verify(:method)` | High | 2 | Verify method was called |
| MOCK-008 | `.called()` | High | 1 | Check if method was called |
| MOCK-009 | `.calledTimes(n)` | Medium | 1 | Check exact call count |
| MOCK-010 | `.calledWith(args)` | Medium | 2 | Check specific arguments |
| MOCK-011 | `any()` matcher | Medium | 1 | Match any argument |
| MOCK-012 | `gt(x)`, `lt(x)`, etc | Low | 2 | Comparison matchers |

---

## Completed CLI Features

| Feature ID | Feature | Importance | Difficulty | Description |
|------------|---------|------------|------------|-------------|
| CLI-001 | `simple test` command | High | 3 | Unified test runner |
| CLI-002 | `--unit` flag | High | 1 | Run unit tests |
| CLI-003 | `--integration` flag | High | 1 | Run integration tests |
| CLI-004 | `--system` flag | High | 1 | Run system tests |
| CLI-005 | `--tag <name>` | Medium | 2 | Filter by tag (parsed) |
| CLI-006 | `--fail-fast` | Medium | 1 | Stop on first failure |
| CLI-007 | `--seed N` | Low | 1 | Deterministic shuffle |
| CLI-008 | `--format json` | Medium | 2 | JSON output for machine-readable results |
| CLI-009 | `--format doc` | Low | 2 | Nested documentation output (RSpec-style) |

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

## Completed Contract Features

### Core Contract Blocks

| Feature ID | Feature | Importance | Difficulty | Description |
|------------|---------|------------|------------|-------------|
| CTR-001 | `in:` preconditions | High | 3 | Boolean expressions at function entry |
| CTR-002 | `out(ret):` postconditions | High | 3 | Conditions on success return |
| CTR-003 | `out_err(err):` | High | 3 | Conditions on error return |
| CTR-004 | `invariant:` routine | High | 3 | Must hold at entry and all exits |

---

## Completed Formal Verification

### Contract Verification

| Feature ID | Description | Importance | Difficulty | Status |
|------------|-------------|------------|------------|--------|
| FV-100 | Precondition semantics (`in:`) | High | 3 | ✅ |
| FV-101 | Postcondition semantics (`out(ret):`) | High | 3 | ✅ |
| FV-102 | Error postcondition semantics (`out_err(err):`) | High | 3 | ✅ |
| FV-103 | Routine invariant preservation | Medium | 3 | ✅ |
| FV-104 | `old(expr)` snapshot correctness | Medium | 2 | ✅ |

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
