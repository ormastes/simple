---
id: spec_matcher_nested_call_dispatch_2026-07-27
status: OPEN
severity: high
discovered: 2026-07-27
discovered_by: lane SPECM while triaging test/01_unit/lib/ecs/ecs_spec.spl
related: src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs
related: src/compiler_rust/compiler/src/interpreter_method/mod.rs
related: test/01_unit/lib/ecs/ecs_spec.spl
family: interp_enum_method_nested_call_dispatch_2026-06-29
---

# BDD matchers (`to_equal`, `to_be`, ...) are unresolvable in nested call context

## Symptom

```
semantic: method 'to_equal' not found on value of type i64 in nested call context
semantic: method 'to_equal' not found on value of type bool in nested call context
```

## Breaking expression shape

A matcher method chained directly onto the result of a **user-defined method
call**:

```
<recv>.<method>(<args>).to_equal(<expected>)
```

`expect` is *not* part of the trigger. All three of these fail identically:

| shape | verdict |
|---|---|
| `expect alloc.len().to_equal(2)`   | FAIL — method not found |
| `expect(alloc.len().to_equal(2))`  | FAIL — method not found |
| `val r = alloc.len().to_equal(2)`  | FAIL — method not found |
| `expect(alloc.len()).to_equal(2)`  | OK (canonical form) |
| `expect a.id.to_equal(0)`          | OK — field receiver, not a call |
| `expect n.to_equal(0)`             | OK — local variable receiver |

Minimal repro: `build/specm_repro/g_spec.spl` (G1/G2 red, G3 green).

## Root cause (library vs compiler: **compiler**)

`std.spec` does not implement the matchers at all — `to_equal`/`to_be`/
`to_contain`/... are builtins in the Rust seed interpreter,
`src/compiler_rust/compiler/src/interpreter_method/mod.rs:277-330`, which
applies them to any `recv_val` and sets `BDD_EXPECT_FAILED`/`BDD_FAILURE_MSG`.

The chained/nested-call dispatcher
`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`
(`call_method_on_value`, error at line 817) walks: impl methods -> UFCS free
function -> bare-payload Option/Result convention -> hard error. It never
consults the BDD matcher table. Any matcher reaching that path therefore dies
with METHOD_NOT_FOUND instead of running.

Same family as `interp_enum_method_nested_call_dispatch_2026-06-29`,
`interp_chained_replace_2026-07-05`,
`web_font_provider_split_nested_call_resolution_2026-07-14` — the nested-call
dispatcher is a parallel, under-populated copy of the main method table.

## Why it matters (coverage impact)

The paren-less `expect X.to_equal(Y)` form does *not* mean
`expect(X).to_equal(Y)`; it parses as `expect(X.to_equal(Y))`. When it happens
to resolve, the matcher runs against the raw value and the outer `expect`
degrades to a truthiness check, so the failure message becomes
`expected call result to be truthy, got false` instead of
`expected 1 to equal 2`. When it does *not* resolve (call receiver), the example
goes red for a reason unrelated to the code under test — which is how a genuine
`EntityAllocator` generation bug hid behind a harness error for the whole life of
`ecs_spec.spl` (see `ecs_entity_generation_not_bumped_on_reuse_2026-07-27`).

## Blast radius

`173` occurrences across `27` spec files use a matcher chained onto a method-call
result:

```
grep -rnE '[A-Za-z0-9_])]\.[A-Za-z0-9_]+\([^()]*\)\.to_(equal|be|contain|include|start_with|end_with|not_)' \
  --include='*_spec.spl' test/ src/
```

(escape the char class as `[A-Za-z0-9_\]\)]`). Worst offenders:
`test/integration/os/port/llvm/per_target_build_spec.spl` (31),
`test/01_unit/lib/crypto/ml_kem_768_kat_spec.spl` (21),
`test/integration/os/port/llvm/cross_build_plan_spec.spl` (15),
`test/unit/lib/ecs/ecs_spec.spl` (13, stale duplicate of the 01_unit file).
`test/system/os/port/disk_boot_spec.spl:121` has a bare
`out.contains("[BOOT]").to_equal(true)` with no `expect` at all.

## Fix sketch (NOT applied — compiler trees owned by other lanes)

In `call_method_on_value`, before the METHOD_NOT_FOUND error, delegate the BDD
matcher names to the same handler used by `interpreter_method/mod.rs` (or hoist
that match arm into a shared helper so the two dispatchers cannot drift again).

Workaround until then: always write the canonical `expect(<value>).to_matcher(...)`
form — never chain a matcher onto a method call.
