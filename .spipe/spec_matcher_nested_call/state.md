# Lane SPECM — spec matcher in nested call context

Date: 2026-07-27
Status: DONE (spec fixed; two bugs filed, neither patched — both outside lane scope)

## Breaking shape

`<recv>.<method>(<args>).to_equal(<expected>)` — a BDD matcher chained directly
onto the result of a **user-defined method call**. `expect` is irrelevant to the
trigger; `val r = alloc.len().to_equal(2)` fails identically. Field receivers
(`a.id.to_equal(0)`) and local-variable receivers (`n.to_equal(0)`) resolve fine.
Canonical `expect(alloc.len()).to_equal(2)` is green.

## Root cause: compiler, not std.spec

`std.spec` implements no matchers at all — they are seed-interpreter builtins in
`src/compiler_rust/compiler/src/interpreter_method/mod.rs:277-330`. The nested/
chained dispatcher `interpreter_helpers/method_dispatch.rs::call_method_on_value`
(error at line 817) never consults that table, so a matcher on a call result
hits METHOD_NOT_FOUND. Same family as the 2026-06-29 / 2026-07-05 / 2026-07-14
"nested call context" bugs. Not patched — compiler trees are owned by JITCA/PMR.

Secondary coverage hazard: paren-less `expect X.to_equal(Y)` parses as
`expect(X.to_equal(Y))`. When it resolves, the matcher runs on the raw value and
the outer `expect` degrades to a truthiness check — the assertion still fires but
the diagnostic collapses to "expected call result to be truthy, got false".

## Work done

- `test/01_unit/lib/ecs/ecs_spec.spl`: all 32 assertions converted from
  paren-less `expect X.to_equal(Y)` to canonical `expect(X).to_equal(Y)`.
  No assertion deleted, loosened, or re-targeted.
- Filed `doc/08_tracking/bug/spec_matcher_nested_call_dispatch_2026-07-27.md`.
- Filed `doc/08_tracking/bug/ecs_entity_generation_not_bumped_on_reuse_2026-07-27.md`.
- Repros kept in `build/specm_repro/` (`g_spec.spl` = minimal, `h_spec.spl` = ECS probe).

## ecs_spec verdict

Before: 6 failures, all `method 'to_equal' not found ... in nested call context`.
After: 5 of 6 green; 1 example fails honestly —
"bumps generation on reuse so stale handles do not alias", `expected true to
equal false`. That is a **real `EntityAllocator` defect** the harness error had
been masking (`generations[]` doubles as the free-list link, so `free` destroys
the generation and reuse recomputes the same value). `src/lib/*/ecs/**` is out of
lane scope, so it is filed, not fixed, and the assertion is deliberately left red.

Per-describe: 4ex/1fail, 3ex/0, 2ex/0, 1ex/0, 1ex/0.

## No-regression

`test/01_unit/os/arch/duplicate_owner_spec.spl` 4/0 + 2/0.
`test/01_unit/os/services/ds_service_spec.spl` 2/0 x2, 3/0, 2/0 x3.

## Blast radius

173 occurrences in 27 spec files use the breaking shape (matcher chained onto a
method-call result). Top: `test/integration/os/port/llvm/per_target_build_spec.spl`
(31), `test/01_unit/lib/crypto/ml_kem_768_kat_spec.spl` (21),
`test/integration/os/port/llvm/cross_build_plan_spec.spl` (15),
`test/unit/lib/ecs/ecs_spec.spl` (13 — stale duplicate tree, not touched).
`test/system/os/port/disk_boot_spec.spl:121` has a matcher with no `expect` at all.

## Environment note

`bin/simple` currently resolves to a **Rust bootstrap seed** (it prints the
"do not use as the normal tool" warning). `SIMPLE_EXECUTION_MODE=interpreter`
produced identical results on every repro, so the two engines do not differ here.
