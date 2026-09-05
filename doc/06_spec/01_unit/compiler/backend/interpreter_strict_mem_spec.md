# Pure-Simple interpreter strict-memory mode (M5 parity with SIMPLE_STRICT_MEM)

> The Rust seed's tree-walking interpreter has a strict mode (`SIMPLE_STRICT_MEM=1`, see `src/compiler_rust/compiler/src/value.rs` `strict_mem_enabled()` / `CowEnv::mark_uninit`) that traps a read of an initializer-less `let`/`var` binding because it operates on the raw AST, where `let_stmt.value: Option<Expr>` still distinguishes "no initializer" from an explicit `= nil`. This spec drives the equivalent gate added to the pure-Simple tree-walking interpreter (`InterpreterBackendImpl`/ `Environment`, `src/compiler/70.backend/backend/`):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure-Simple interpreter strict-memory mode (M5 parity with SIMPLE_STRICT_MEM)

The Rust seed's tree-walking interpreter has a strict mode (`SIMPLE_STRICT_MEM=1`, see `src/compiler_rust/compiler/src/value.rs` `strict_mem_enabled()` / `CowEnv::mark_uninit`) that traps a read of an initializer-less `let`/`var` binding because it operates on the raw AST, where `let_stmt.value: Option<Expr>` still distinguishes "no initializer" from an explicit `= nil`. This spec drives the equivalent gate added to the pure-Simple tree-walking interpreter (`InterpreterBackendImpl`/ `Environment`, `src/compiler/70.backend/backend/`):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / Interpreter backend |
| Status | Active |
| Source | `test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The Rust seed's tree-walking interpreter has a strict mode
(`SIMPLE_STRICT_MEM=1`, see `src/compiler_rust/compiler/src/value.rs`
`strict_mem_enabled()` / `CowEnv::mark_uninit`) that traps a read of an
initializer-less `let`/`var` binding because it operates on the raw AST,
where `let_stmt.value: Option<Expr>` still distinguishes "no initializer"
from an explicit `= nil`. This spec drives the equivalent gate added to the
pure-Simple tree-walking interpreter (`InterpreterBackendImpl`/
`Environment`, `src/compiler/70.backend/backend/`):

- default OFF (`SIMPLE_STRICT_MEM` unset / not `"1"`): reading an
  initializer-less `var` binding returns the placeholder `Value.Nil`, exactly
  as before this change.
- ON (`ctx.strict_mem == true`): the same read instead returns an
  `Err(BackendError.runtime_error(...))` naming the variable and saying it is
  uninitialized.
- a subsequent real write clears the trap so later reads succeed again.

## A note on how this spec builds its fixtures

This spec seeds `Environment.scopes` and calls `Environment.mark_uninit` /
`clear_uninit` directly, and drives `InterpreterBackendImpl.eval_expr`
directly (the same "call backend methods directly" idiom
`interpreter_backend_spec.spl` already uses for `eval_binop`) rather than
going through `InterpreterBackendImpl.exec_stmt` on a hand-built
`HirStmtKind.Let`/`Assign` node. That is a deliberate workaround, not a
style choice: `Environment.define`/`assign` (env.spl) both write through a
CHAINED double index (`self.scopes[last_idx][name] = value`), and the
`bin/simple test` execution engine that runs THIS spec file is itself the
seed's tree-walk interpreter (`doc/07_guide/infra/testing.md`: "`bin/simple
test` hard-defaults to the tree-walk interpreter"). That engine has a known,
already-filed, pre-existing gap rejecting exactly that shape of
lvalue --
`doc/08_tracking/bug/pure_simple_divergence_domains_2026-07-29.md`, row
`p10a_nested_index_assign`: "rejects `grid[0][1] = 99` outright ... feature
gap" (single-index assignment on a plain identifier or a field access is
unaffected and is used freely below). It is unrelated to this change and
predates it by a day; `interpreter_backend_spec.spl`'s own passing tests
already avoid `exec_stmt`/`env.define()` for the same reason (its closure
test builds `env.scopes = [outer_scope, inner_scope]` directly instead).
The `HirStmtKind.Let`/`Assign` -> `mark_uninit`/`clear_uninit` call sites
added in `interpreter.spl` are one-line, directly-inspectable hookups onto
the independently-tested primitives below.

## Scenarios

### interp_is_uninit_marker_init classifies a Let init expression

#### true for a bare NilLit (what an initializer-less var lowers to)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- true for a bare NilLit (what an initializer-less var lowers to)
   - Expected: interp_is_uninit_marker_init(nil_init) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true for a bare NilLit (what an initializer-less var lowers to)")
val sp = Span.default()
val nil_init = HirExpr(kind: HirExprKind.NilLit, type_: nil, span: sp)
expect(interp_is_uninit_marker_init(nil_init)).to_equal(true)
```

</details>

#### false for a real value

- false for a real value
   - Expected: interp_is_uninit_marker_init(int_init) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false for a real value")
val sp = Span.default()
val int_init = HirExpr(kind: HirExprKind.IntLit(42, nil), type_: nil, span: sp)
expect(interp_is_uninit_marker_init(int_init)).to_equal(false)
```

</details>

### Environment strict-mem uninit tracking (mark_uninit/is_uninit/clear_uninit)

#### a name is not uninit until marked

- a name is not uninit until marked
   - Expected: env.is_uninit("x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a name is not uninit until marked")
var env = Environment.new()
expect(env.is_uninit("x")).to_equal(false)
```

</details>

#### mark_uninit makes is_uninit true

- mark_uninit makes is_uninit true
   - Expected: env.is_uninit("x") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mark_uninit makes is_uninit true")
var env = Environment.new()
env.mark_uninit("x")
expect(env.is_uninit("x")).to_equal(true)
```

</details>

#### clear_uninit undoes mark_uninit

- clear_uninit undoes mark_uninit
   - Expected: env.is_uninit("x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear_uninit undoes mark_uninit")
var env = Environment.new()
env.mark_uninit("x")
env.clear_uninit("x")
expect(env.is_uninit("x")).to_equal(false)
```

</details>

### Pure-Simple interpreter strict-mem (SIMPLE_STRICT_MEM parity)

#### default OFF: reading an uninitialized var returns Value.Nil, unchanged

- default OFF: reading an uninitialized var returns Value.Nil, unchanged
   - Expected: got_nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default OFF: reading an uninitialized var returns Value.Nil, unchanged")
val backend = InterpreterBackendImpl.new()
var names: Dict<i64, text> = {}
names[1] = "x"
var scope: Dict<text, Value> = {}
scope["x"] = Value.Nil
var env = Environment.new()
env.scopes = [scope]
val ctx = EvalContext(env: env, module: make_module(), backend: backend, names: names, fn_by_name: {}, has_fn_index: false, strict_mem: false)
# OFF mode: strict_mem is never checked, so an unmarked (or even a
# marked) uninit name never traps -- matches "byte-for-byte unchanged".
val result = backend.eval_expr(read_x_expr(), ctx)
var got_nil = false
match result:
    case Ok(Value.Nil):
        got_nil = true
    case _:
        got_nil = false
expect(got_nil).to_equal(true)
```

</details>

#### ON: reading an uninitialized var traps with a clear diagnostic

- ON: reading an uninitialized var traps with a clear diagnostic
   - Expected: trapped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ON: reading an uninitialized var traps with a clear diagnostic")
val backend = InterpreterBackendImpl.new()
var names: Dict<i64, text> = {}
names[1] = "x"
var scope: Dict<text, Value> = {}
scope["x"] = Value.Nil
var env = Environment.new()
env.scopes = [scope]
env.mark_uninit("x")
val ctx = EvalContext(env: env, module: make_module(), backend: backend, names: names, fn_by_name: {}, has_fn_index: false, strict_mem: true)
val result = backend.eval_expr(read_x_expr(), ctx)
var trapped = false
match result:
    case Err(err):
        trapped = err.message.contains("strict-mem") and err.message.contains("uninitialized") and err.message.contains("x")
    case Ok(_):
        trapped = false
expect(trapped).to_equal(true)
```

</details>

#### ON: a cleared-uninit binding with a real value reads normally (not trapped)

- ON: a cleared-uninit binding with a real value reads normally (not trapped)
   - Expected: got_seven is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ON: a cleared-uninit binding with a real value reads normally (not trapped)")
# `mark_uninit` then `clear_uninit` -- exactly the sequence
# `HirStmtKind.Let` then a later `HirStmtKind.Assign` arm drives in
# interpreter.spl -- leaves `is_uninit("x")` false (independently
# proven in the "Environment strict-mem uninit tracking" describe
# block above), so a read of the real value bound to `x` must
# succeed rather than trap.
val backend = InterpreterBackendImpl.new()
var names: Dict<i64, text> = {}
names[1] = "x"
var scope: Dict<text, Value> = {}
scope["x"] = Value.Int(7)
var env = Environment.new()
env.scopes = [scope]
env.mark_uninit("x")
env.clear_uninit("x")
val ctx = EvalContext(env: env, module: make_module(), backend: backend, names: names, fn_by_name: {}, has_fn_index: false, strict_mem: true)
val result = backend.eval_expr(read_x_expr(), ctx)
var got_seven = false
match result:
    case Ok(Value.Int(v)):
        got_seven = v == 7
    case _:
        got_seven = false
expect(got_seven).to_equal(true)
```

</details>

#### ON: a genuinely-initialized var (never marked) is never trapped

- ON: a genuinely-initialized var (never marked) is never trapped
   - Expected: got_42 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ON: a genuinely-initialized var (never marked) is never trapped")
val backend = InterpreterBackendImpl.new()
var names: Dict<i64, text> = {}
names[1] = "x"
var scope: Dict<text, Value> = {}
scope["x"] = Value.Int(42)
var env = Environment.new()
env.scopes = [scope]
val ctx = EvalContext(env: env, module: make_module(), backend: backend, names: names, fn_by_name: {}, has_fn_index: false, strict_mem: true)
val result = backend.eval_expr(read_x_expr(), ctx)
var got_42 = false
match result:
    case Ok(Value.Int(v)):
        got_42 = v == 42
    case _:
        got_42 = false
expect(got_42).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cb16f35c6c9c0727e1e88cb35432d8ca4e758f024ee82199e99b3dfedce55558`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb16f35c6c9c0727e1e88cb35432d8ca4e758f024ee82199e99b3dfedce55558`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb16f35c6c9c0727e1e88cb35432d8ca4e758f024ee82199e99b3dfedce55558`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/interpreter_strict_mem_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/interpreter_strict_mem_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/interpreter_strict_mem_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'true for a bare NilLit (what an initializer-less var lowers to)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'false for a real value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a name is not uninit until marked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
