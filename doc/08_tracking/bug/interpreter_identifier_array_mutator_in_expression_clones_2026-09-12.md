# Interpreter: `arr.pop()` nested inside an expression clones the whole array per call

- Status: RESOLVED (2026-09-12) — fixed on `work/interp-expr-mutator`
- Found: 2026-09-12, interpreter component scaling probes (batch 4)
- Component: seed tree-walk interpreter — `src/compiler_rust/compiler/src/interpreter/expr/calls.rs`
  (`Expr::MethodCall` with an `Expr::Identifier` receiver, expression context)
- Lane: interpreter only (`bin/simple test` lane); JIT flat.

## Summary

A mutating array method on a plain local variable is O(1)-amortized when the
call is a statement (`arr.pop()`) or an initializer (`val x = arr.pop()`):
those route through `interpreter_helpers/patterns.rs`'s identifier fast path,
which mutates through the single owner in the env slot with `Arc::make_mut`.
The same call **nested in any larger expression** — `acc + arr.pop()`,
`f(arr.pop())`, `if arr.pop() % 2 == 0` — is evaluated by
`interpreter/expr/calls.rs`, whose identifier branch only has the MECALL-OWNED
move for `Value::Object` receivers (`owned_call`). An `Value::Array` receiver
falls to `evaluate_method_call_with_self_update`, which evaluates the receiver
to a COPY (`Arc` refcount 2), so `handle_array_methods`' `pop` arm clones the
whole backing `Vec` (`to_vec()`) before removing one element: O(n) per call,
O(n^2) per loop. `push` in expression context shares the shape but is rarely
written that way (`push` returns nothing useful); `pop`/`remove`/`insert` are.

## Evidence (deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, 2026-09-06 09:59, 50,093,192 B; interpreter lane; 4x n, linear = 4)

| loop body | n=20000 | n=80000 | ratio |
|---|---:|---:|---:|
| `arr.pop()` (statement) | 0.06 s | 0.20 s | 3.3 |
| `val x = arr.pop(); acc = acc + x` | 0.08 s | 0.30 s | 3.8 |
| `acc = acc + arr.pop()` | 1.35 s | 15.80 s | **11.7** |
| `acc = acc + id(arr.pop())` | 0.94 s | 19.36 s | **20.6** |
| `if arr.pop() % 2 == 0:` | 1.21 s | 21.23 s | **17.5** |
| `arr.push(i); acc = acc + arr.len()` (control) | 0.05 s | 0.18 s | 3.6 |

`SIMPLE_PERF_COUNTERS=1`: `ARR_MUT_CALLS=20000`, no `ARR_MUT_COW_*` — the
clone happens in the un-instrumented `to_vec()` arm, not the COW path.

## Fix direction

In `calls.rs`'s identifier branch, when the variable holds a `Value::Array`
(or `Dict`) and `method` is a mutator, route to the SAME in-place kernel the
statement path uses (one kernel, no third copy of the logic) and return its
result; everything else unchanged. Pin with an `it` in
`test/05_perf/interp/interpreter_component_scaling_spec.spl`
("pop_in_expression") plus the existing aliasing pins.

## Fix landed (2026-09-12)

`src/compiler_rust/compiler/src/interpreter/expr/calls.rs:172-215` (new gate +
routing call, inserted before the pre-existing
`evaluate_method_call_with_self_update` fallback);
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:176-187`
(`ARRAY_MUTATING_METHODS` visibility widened from private to `pub(crate)`,
with a comment explaining why calls.rs needs it and the recursion risk of
using it wrong).

`interpreter/expr/calls.rs`'s `Expr::MethodCall` identifier branch now checks,
right before the generic `evaluate_method_call_with_self_update` fallback,
whether the receiver holds a `Value::Array` AND `method` is in
`ARRAY_MUTATING_METHODS` (made `pub(crate)`, was private, so `calls.rs` can
share the gate `interpreter_helpers::patterns` already uses). When both hold,
the call is routed through
`interpreter_helpers::patterns::handle_method_call_with_self_update(expr, ...)`
— the exact function the statement fast path (`node_exec.rs`, `block_exec.rs`)
already calls, which mutates the env slot's `Arc<Vec<Value>>` in place via
`Arc::make_mut` and syncs MODULE_GLOBALS itself. No new kernel was written.

**Dict was deliberately excluded.** Reading `patterns.rs`'s own identifier
branch showed its Dict-mutator arm (~L1525) has no in-place kernel of its
own — it delegates back to `evaluate_expr(value_expr, ...)`, which dispatches
straight to `eval_call_expr` (i.e. `calls.rs`'s own identifier branch).
Routing `Value::Dict` through `handle_method_call_with_self_update` from
`calls.rs` would therefore recurse forever (`calls.rs` -> `patterns.rs` Dict
arm -> `evaluate_expr` -> `calls.rs` -> ...). The gate is `Value::Array` only,
which also closes the analogous risk for a non-mutating array method
(`arr.len()`): `patterns.rs`'s Array arm falls through to the same
`evaluate_expr` recursion for anything outside `ARRAY_MUTATING_METHODS`, so
gating on the mutator set (not just "is an Array") is what keeps this fix
one-directional. This is a scoping decision from reading the code, not a
measured defect: BRIEF.md's own probe table shows STATEMENT-context
`dict_insert_local` scaling linearly (ratio 3-4.3), so something elsewhere
(likely `evaluate_method_call_with_self_update` itself, or a different branch
this investigation didn't trace) already handles that shape without the
clone the code-reading above would predict. Expression-context dict mutators
(`acc = acc + d.remove(k)`-shaped code) were NOT measured in this lane and are
left unprobed; if a real defect is found there later, file it separately
against `patterns.rs`'s Dict arm rather than reopening this record.

## Results (red -> green)

Binaries:
- Deployed seed (RED): `bin/release/aarch64-unknown-linux-gnu/simple`, 2026-09-06 09:59:11, 50,093,192 B.
- Rebuilt candidate (GREEN): `src/compiler_rust/target/release/simple` (work/interp-expr-mutator), 2026-09-12 10:10:05, 51,225,464 B.

New spec: `test/05_perf/interp/identifier_mutator_in_expression_scaling_spec.spl`
(n=20000 vs n=80000, bound `large*10 < small*70` i.e. ratio < 7):

| shape | seed (RED) n=20000 | seed (RED) n=80000 | seed ratio | candidate (GREEN) n=20000 | candidate (GREEN) n=80000 | candidate ratio |
|---|---:|---:|---:|---:|---:|---:|
| `acc = acc + arr.pop()` | 1.296060 s | 19.906351 s | 15.4 | 0.128197 s | 0.172452 s | 1.35 |
| `acc = acc + id(arr.pop())` | 1.349556 s | 18.142913 s | 13.4 | 0.190593 s | 0.818152 s | 4.29 |
| `if arr.pop() % 2 == 0:` | 1.124832 s | 19.956915 s | 17.7 | 0.110405 s | 0.227206 s | 2.06 |

Aliasing correctness (`val alias = arr` before an expression-context pop loop
drains `arr`) passed on BOTH binaries — the COW guarantee was never broken,
only the amortized cost of the unaliased fast path.

Spec result: 4/4 passed on the candidate (0/4 ratio its passed on the seed;
aliasing `it` passed on both). Rust unit tests, candidate binary:
`cargo test --release -p simple-compiler --lib patterns` 31/31 passed
(including `cow_alias_mechanism_tests::*`); `--lib calls` 146/146 passed;
`--lib collections` 33/33 passed. Correctness pin
`test/01_unit/lib/common/array_field_push_interpreter_perf_spec.spl` 4/4
passed. `test/01_unit/interpreter/` 8/8 passed. `test/01_unit/language/`
176/182 passed, 6 failed, 5 skipped — all 6 failures reproduce identically
(same file, same count, same assertions) on the unmodified deployed seed, so
none are a regression from this change:
`primitive_receiver_trait_impl_dispatch_spec.spl`,
`if_val_binding_shadows_module_global_spec.spl`,
`engine_divergence_mutation_class_spec.spl`,
`primitive_receiver_trait_impl_dispatch_class_spec.spl`.

`sh scripts/check/check-perf-regression-tests.shs` after adding four
`ARRAYMUTEXPR` mechanism rows (`ROW_FLOOR` raised 147 -> 195, actual count
195): same 4 pre-existing regressions as `main`
(`pure-interp array push through owner`, `HOPPARK test pins clone budget at
every depth`, `ANYVTJIT seed: aggregate copy keeps vtable hdr`,
`IMPORTASTMEMO seed: memo cleared with the loader caches`), 0 new.

**Store-sync note (not a regression, unverified corner):** the pre-existing
`Value::Object` MECALL-OWNED path a few lines above this fix writes non-local
receivers back via `write_back_identifier_receiver`, whose owner comes from
`env.global_binding(name)`. The new Array path instead goes through
`handle_method_call_with_self_update`'s wrapper, which resolves the owner via
`CURRENT_EXEC_MODULE` (`sync_flat_global`) — identical to what the
STATEMENT-context fast path has always done for arrays, so this is "same
kernel by construction," not new behavior. For a module global mutated inside
its own defining module the two owner-resolution strategies coincide; an
imported global mutated inside a different module (`use A.{g}` then
`acc = acc + g.pop()` in module B) was not separately probed by
`test/01_unit/language` or the new spec, so that specific cross-module shape
is unverified here (it was equally unverified on the statement path before
this change).

## Related

- `interpreter_nested_place_mutation_clones_container_2026-09-12.md` (same
  family: receiver evaluated to a copy before mutation)
