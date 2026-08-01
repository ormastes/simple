# Known tool defects (OPEN) — discovered by the validation corpus

These `.spl` files are **reproducible repros of real defects** in the deployed
pure-Simple compiler (`bin/release/x86_64-unknown-linux-gnu/simple`), found while
standing up the tool-qualification corpus. Each is a program that a
safety-critical (DO-330 Criterion-1) tool **should reject** but which the
deployed binary **silently accepts**. That is failure mode **TOR-FM-02**
(silent accept of a bad program) from the tool qualification plan.

They are **NOT** gated by `run-tool-qual-corpus.shs` — a perpetually-red gate is
not the goal. They are durable, hand-verifiable evidence and seed the plan's
`known_problem/` category / `tool_known_problems` ledger (plan §3.1). Reproduce
any of them with:

```
bin/release/x86_64-unknown-linux-gnu/simple run <file>.spl ; echo "exit=$?"
```

| Repro | Should happen | Actually happens (deployed binary) | Severity |
|---|---|---|---|
| `arity_too_many.spl` | reject: `add/2` called with 3 args | accepted, extra arg dropped, prints `3`, exit 0 | high |
| `arity_too_few.spl` | reject: `add/2` called with 1 arg | accepted, prints `1`, exit 0 | high |
| `arg_type_mismatch.spl` | reject: text passed where `i64` expected | accepted, prints GARBAGE (raw text pointer as int, e.g. `6295919127139`), exit 0 | **critical (memory/type-safety hole)** |
| `undefined_type_annotation.spl` | reject: `val x: Nonexistent` names no type | accepted, prints `5`, exit 0 | medium |
| `nonexhaustive_match.spl` | reject/trap: `match` has no arm for `E.B` | accepted, `f(E.B)` returns `0`, exit 0 | high |
| `trait_default_method_inherited_segfault.spl` | run: call an inherited (non-overridden) trait default method | SEGFAULT, exit 139 | **critical (crash)** |
| `mixin_class_use_garbage_value.spl` | run: `class X: use Mixin` injected method/field return their real values | accepted, prints a raw heap-value tag and `0.0` instead of `15`/`Alice`, exit 0 | **critical (memory-safety hole)** |
| `mixin_struct_use_runtime_error.spl` | run (or reject): `struct X: use Mixin` injected method | accepted, leaks a fabricated `"error"` string + `0` to stdout while a "Function not found" diagnostic goes to stderr, exit 0 | high |
| `nested_closure_capture_wrong_value.spl` | run: a closure nested in another closure reads the outer closure's captured var | accepted, silently computes `0` instead of `36`, exit 0 | high |
| `closure_return_across_function_boundary_invalid_heap.spl` | run: a closure capturing a fn parameter, returned to the caller, computes correctly | accepted, prints an invalid-heap-pointer tag instead of `105`, exit 0 | **critical (memory-safety hole)** |

For contrast, the following ARE correctly rejected (they live in `../negative/`
and pass the gate): undefined variable, unknown struct field, undefined
function call, parse error (unclosed paren / missing colon), undefined struct
type, undefined module import, reserved keyword as identifier.

**Interpretation.** Name resolution rejects *unknown* symbols/fields/functions/
types/modules and most parse errors, but the type/arity checker does **not**
reject *arity* mismatches, *argument-type* mismatches, *unknown type
annotations*, or *non-exhaustive matches* — these reach codegen and execute
with wrong/garbage semantics. Two further construct families are unsound at
runtime rather than at accept-time: **mixin composition** (`use Mixin` inside
`class`/`struct`) produces garbage values or leaked error strings instead of
working or being rejected, and **closures that are lexically nested or that
escape their defining function** either segfault, compute silently-wrong
values, or return invalid-heap-pointer tags. The `arg_type_mismatch` and
`closure_return_across_function_boundary_invalid_heap` cases are the most
serious: both are unsound accepts that read raw memory as a typed value,
exactly the class of latent product defect DO-330 tool qualification exists to
prevent. Until each is fixed (or waived with justification), the tool is **not**
qualifiable at Criterion 1 for the required functions TOR-F2 (type-check) and
TOR-F3 (codegen soundness for traits/mixins/closures).
