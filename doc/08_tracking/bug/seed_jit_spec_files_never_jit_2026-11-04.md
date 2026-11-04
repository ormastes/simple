# Seed JIT never executes spec files (silent `jit-bail:no-main-fn`) + std.spec closure refusals

- **Date:** 2026-11-04
- **Area:** seed (`src/compiler_rust`) — `driver/src/exec_core.rs` (`run_file_jit`), `compiler/src/codegen/jit.rs` (`first_unsupported_lambda`)
- **Status:** partially fixed. The fallback is now visible and fatal under strict mode, and the std.spec closure refusals are fixed. Spec-entry synthesis is implemented but OPT-IN (`SIMPLE_JIT_SPEC_ENTRY=1`) because the compiled rt_bdd lane fails specs that pass on the interpreter (measured below).
- **Found by:** PR #6634 report ("spec file still interprets: `jit-bail:no-main-fn`; std.spec `skip` closure is a separate JIT ABI refusal")

## Symptoms

1. A `*_spec.spl` has no `fn main`. `run_file_jit` checked for `main` after MIR
   lowering, recorded the demotion `jit-bail:no-main-fn` in the engine receipt,
   and ran the whole module on the interpreter. Nothing on stdout/stderr said
   so, and `SIMPLE_JIT_STRICT=1` did not stop it. `simple run <spec>` in JIT mode
   and the runner's JIT lane never executed a spec on the JIT.
2. Every module that imports `std.spec` got refused as a whole by
   `first_unsupported_lambda`, for two reasons:
   - `decorators.spl` `skip(...) -> fn(text, fn())` returns a closure. The
     guard refused every closure return. The measured defect is only the
     `any`-typed return slot, whose `BoxInt` shifts the handle.
   - `skip_if(condition: fn() -> bool, ...)` calls `condition()`, an
     `IndirectCall` with a `BOOL` result. Also, `block()` on a `fn()` has a
     `VOID` result. The guard refused both, but the call site already handles
     both: `compile_indirect_call` skips unboxing for VOID, and
     `unbox_from_closure_boundary` reads BOOL as a full-width value
     compared against 0. The documented BOOL SIGSEGV happens when the outlined
     BODY is declared `i8`. `shared.rs` still keeps such bodies at I64.

## Fix

- `synthesize_spec_main` (exec_core.rs) is gated on `SIMPLE_JIT_SPEC_ENTRY=1` and only runs for a module with no `main`
  that declares module-level BDD examples. It moves the module-level executable
  statements into a synthesized `fn main() -> i64` and leaves
  `val`/`var`/`const`/`static` bindings and declarations as globals. HIR then
  lowers `describe`/`it`/`expect` to the `rt_bdd_*` runtime, which is the
  compiled-spec lane.
- `finish_jit_spec_entry` takes the `rt_bdd_*` totals, records each example in
  the shared BDD result table (`record_external_test_result`), which drives
  `SPEC FILE VERDICT` and the `SIMPLE_TEST_RESULT_FILE` evidence. It returns
  exit code 1 if any example failed and prints
  `[jit-spec-entry] <path> executed on cranelift-jit: P passed, F failed`.
- The no-`main` interpreter fallback that remains (plain scripts) now prints
  `[jit-fallback] jit-bail:no-main-fn ...` and becomes a hard error under
  `SIMPLE_JIT_STRICT=1`.
- `first_unsupported_lambda` now refuses a returned closure only when the
  function's return type is `ANY`, and accepts VOID/BOOL call results.
  Fixture `fn mk() -> any: return \x: ...` is still refused, by the
  scalar-boxing check. `fn mk(k) -> fn(i64) -> i64` now runs on the JIT
  (`r=105`).

## Fixed 2026-11-04 (second pass): raw vs tagged matcher operands

Root cause: `rt_bdd_expect_eq_rv`/`rt_bdd_expect_truthy_rv` take tagged
RuntimeValues, but MIR passed typed scalar operands raw (`lower_builtin_call_expr`
generic path). An `any`/optional actual was compared against a raw literal, and
`rv_to_display` guessed tags (`Expected nil to equal 0`, `Expected 1 to equal 0`
for `expect(1).to_equal(2)`). Second cause: `expect(p.?).to_equal(true)` lowered
`.?` in value position (the payload), while the interpreter's
`eval_assertion_operand` reads it as a presence bool.

- `mir/lower/lowering_expr_builtin.rs`: box each matcher operand by static type
  (`box_arg_for_any_param`).
- `hir/lower/stmt_lowering.rs`: `.?` in a `to_equal` operand lowers through
  `lower_condition` (`rt_is_present`).
- Regression: `mir/lower/tests/bdd_matcher_boxing.rs` (2 cargo tests).

Re-measured (`SIMPLE_JIT_SPEC_ENTRY=1 SIMPLE_JIT_STRICT=1`): allocator_pool 4/4,
mimalloc_gc_async_mut_reuse 3/3, lambda_lift_if_enum_capture_scan 8 pass / 1 fail
(same as interpreter), for_in_variant_lowering 8/8, failing fixture prints
"Expected 1 to equal 2".

## Fixed 2026-11-04 (third pass): skip counting on the JIT

HIR lowers a statement call to `skip`/`skip_it`/`pending`/`planned` as
`rt_bdd_note_skip()` plus the original call (new symbol, Rust runtime +
`runtime_native.c` twin). `finish_jit_spec_entry` records each as skipped.
jit_spec_entry_spec now reads `passed=2 skipped=1` on both engines.
Regression: `mir/lower/tests/bdd_skip_count.rs`.

## Remaining gaps (not closed here)

- Some specs still fail under strict mode with
  `unresolved external symbol 'expect'` (and `'fail'` for
  builtin_trait_where_bound_spec) (cross-module Simple function).
  Measured on the `skip_it` fixture. This is the per-module link gap, not the
  entry.
- ~~`skip "name", "reason"` (paren-less, two args) does not parse~~ — decided
  not a bug: the syntax reference (`syntax_quick_reference.md` § No-Paren
  Method Calls, "split needs parens (has arg)") and `doc/07_guide/infra/testing.md`
  only document the single-argument paren-less form (`skip "name":`).
  Multi-argument calls take parentheses: `skip("name", "reason")`.

## Measured verdict parity (worktree seed, `SIMPLE_JIT_STRICT=1`, 2026-11-04)

The JIT rows were taken with synthesis forced on.

| spec | interpreter | JIT (spec entry) |
|---|---|---|
| compiler/jit_spec_entry/jit_spec_entry_spec | 2 pass, 1 skip | 2 pass (skip not counted) |
| jit_spec_entry/fixtures/failing_example (deliberately failing) | 1 fail, rc=1 | 1 fail, rc=1 |
| compiler/20.hir/builtin_trait_where_bound_spec | 4/4 | refused before run (strict compile error) |
| compiler/50.mir/for_in_variant_lowering_spec | 8/8 | 5 pass / 3 fail |
| compiler/50.mir/hwir_riscv_scalar_runtime_completion_selector_spec | rc=1 (0 run) | rc=1 (0 run) |
| compiler/50.mir/lambda_lift_if_enum_capture_scan_spec | 8 pass / 1 fail | 0 pass / 9 fail |
| compiler/50.mir/try_struct_payload_field_for_in_spec | 1/1 | 1/1 |
| lib/alloc/allocator_pool_spec | 4/4 | 0/4 (`Expected nil to equal 0`, `Expected 4795500294561 to equal 1`) |
| lib/alloc/mimalloc_gc_async_mut_reuse_spec | 3/3 | 0/3 |

The JIT failures show raw versus tagged confusion at `rt_bdd_expect_eq_rv`:
the actual values print as nil or huge tagged words. Each of these is a real
compiled-lane bug. They are the reason synthesis stays opt-in. Default-on would
turn interpreter-green runs red for reasons unrelated to the code under test.
Next step: fix value encoding at the `expect(...).to_equal(...)` lowering in
`hir/lower/stmt_lowering.rs` (`try_lower_bdd_matcher_statement`) and
`runtime/src/value/bdd_sffi.rs`, then flip the default.
