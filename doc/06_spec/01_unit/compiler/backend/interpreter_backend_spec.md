# Interpreter Backend Specification

> Tests covering Interpreter Backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Backend Specification

## Scenarios

### Interpreter Backend

#### creates a backend port with stable metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a backend port with stable metadata
   - Expected: backend.name equals `interpreter`
   - Expected: target_triple() equals `interpreter-simple-runtime`
   - Expected: supports_jit() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates a backend port with stable metadata")
val backend = create_interpreter_backend()
val target_triple = backend.target_triple_fn
val supports_jit = backend.supports_jit_fn

expect(backend.name).to_equal("interpreter")
expect(target_triple()).to_equal("interpreter-simple-runtime")
expect(supports_jit()).to_equal(true)
```

</details>

#### returns an independent backend port per factory call

- returns an independent backend port per factory call
   - Expected: first.name equals `second.name`
   - Expected: first_target_triple() equals `second_target_triple()`
   - Expected: first_supports_jit() equals `second_supports_jit()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns an independent backend port per factory call")
val first = create_interpreter_backend()
val second = create_interpreter_backend()
val first_target_triple = first.target_triple_fn
val second_target_triple = second.target_triple_fn
val first_supports_jit = first.supports_jit_fn
val second_supports_jit = second.supports_jit_fn

expect(first.name).to_equal(second.name)
expect(first_target_triple()).to_equal(second_target_triple())
expect(first_supports_jit()).to_equal(second_supports_jit())
```

</details>

#### provides a callable run function

- provides a callable run function
   - Expected: backend.run_fn equals `backend.run_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provides a callable run function")
val backend = create_interpreter_backend()

expect(backend.run_fn).to_equal(backend.run_fn)
```

</details>

#### loads the legacy interpreter backend module

- loads the legacy interpreter backend module
   - Expected: backend.name() equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads the legacy interpreter backend module")
val backend = InterpreterBackendImpl.new()

expect(backend.name()).to_equal("interpreter")
```

</details>

#### rejects a missing binary operator

- rejects a missing binary operator
   - Expected: failed_closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a missing binary operator")
val backend = InterpreterBackendImpl.new()
val result = backend.eval_binop(nil, Value.Int(1), Value.Int(2), Span.default(), false, false)
var failed_closed = false
match result:
    case Err(err):
        failed_closed = err.kind == BackendErrorKind.Internal and err.span.? and err.message.contains("missing HIR binary operator")
    case Ok(_):
        failed_closed = false
expect(failed_closed).to_equal(true)
```

</details>

#### renders str and text builtin arguments

- renders str and text builtin arguments
   - Expected: rendered_str is true
   - Expected: rendered_text is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders str and text builtin arguments")
val backend = InterpreterBackendImpl.new()
var rendered_str = false
match backend.try_call_builtin("str", [Value.Int(7)]):
    case Some(Ok(Value.String(value))):
        rendered_str = value == "7"
    case _:
        rendered_str = false
var rendered_text = false
match backend.try_call_builtin("text", [Value.Bool(true)]):
    case Some(Ok(Value.String(value))):
        rendered_text = value == "true"
    case _:
        rendered_text = false
expect(rendered_str).to_equal(true)
expect(rendered_text).to_equal(true)
```

</details>

#### rejects unknown binary operators before evaluation

- rejects unknown binary operators before evaluation
   - Expected: op_kind_to_binop(60) equals `BinOp.Add`
   - Expected: op_kind_to_binop(9999) equals `BinOp.Invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects unknown binary operators before evaluation")
expect(op_kind_to_binop(60)).to_equal(BinOp.Add)
expect(op_kind_to_binop(9999)).to_equal(BinOp.Invalid)
```

</details>

#### keeps function lookup off shared optional mutation

- keeps function lookup off shared optional mutation
   - Expected: calls_source does not contain `var cf_target: HirFunction? = nil`
   - Expected: calls_source does not contain `cf_target = Some(cf_f)`
   - Expected: interpreter_source does not contain `var cf_named: HirFunction? = nil`
   - Expected: interpreter_source does not contain `cf_named = Some(cf_f2)`
   - Expected: calls_source does not contain `HirFunction? = nil`
   - Expected: interpreter_source does not contain `HirFunction? = nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps function lookup off shared optional mutation")
val calls_source = file_read("src/compiler/70.backend/backend/interpreter_calls.spl")
val interpreter_source = file_read("src/compiler/70.backend/backend/interpreter.spl")

# Neither call site may accumulate the hit into an optional that is
# mutated across loop iterations (the original defect).
expect(calls_source.contains("var cf_target: HirFunction? = nil")).to_equal(false)
expect(calls_source.contains("cf_target = Some(cf_f)")).to_equal(false)
expect(interpreter_source.contains("var cf_named: HirFunction? = nil")).to_equal(false)
expect(interpreter_source.contains("cf_named = Some(cf_f2)")).to_equal(false)
expect(calls_source.contains("HirFunction? = nil")).to_equal(false)
expect(interpreter_source.contains("HirFunction? = nil")).to_equal(false)

# The two former inline `var cf_*_index = -1` scans were centralized into
# one resolver. It must still carry the index-based idiom, and BOTH call
# sites must route through it rather than re-rolling their own scan.
expect(calls_source).to_contain("fn resolve_function_by_name(name: text, ctx: EvalContext) -> HirFunction?:")
expect(calls_source).to_contain("var found_index = -1")
expect(calls_source).to_contain("self.resolve_function_by_name(f_t.name, ctx)")
expect(interpreter_source).to_contain("self.resolve_function_by_name(cname_t, ctx)")
```

</details>

#### uses runtime enum discriminants for struct-shadowed variants

- uses runtime enum discriminants for struct-shadowed variants
   - Expected: source does not contain `fn interp_expr_disc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses runtime enum discriminants for struct-shadowed variants")
val source = file_read("src/compiler/70.backend/backend/interpreter.spl")
expect(source).to_contain("val ee_disc: i64 = rt_enum_discriminant(expr.kind)")
expect(source).to_contain("if ee_disc == 1138084884:  # hash(\"Block\")")
expect(source).to_contain("val stmt_disc = rt_enum_discriminant(stmt.kind)")
expect(source.contains("fn interp_expr_disc")).to_equal(false)
expect(source.index_of("case HirExprKind.NilLit:")).to_be_greater_than(source.index_of("case HirExprKind.Call(callee, args, _):"))
```

</details>

#### pops scopes through the core-array ABI

- pops scopes through the core-array ABI
   - Expected: source does not contain `self.scopes = self.scopes[0:last_idx]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pops scopes through the core-array ABI")
val source = file_read("src/compiler/70.backend/backend/env.spl")
expect(source).to_contain("self.scopes.pop()")
expect(source.contains("self.scopes = self.scopes[0:last_idx]")).to_equal(false)
```

</details>

#### tears down a popped scope so its names stop resolving

- tears down a popped scope so its names stop resolving
   - Expected: env.scopes.len() equals `2`
   - Expected: env.scopes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tears down a popped scope so its names stop resolving")
# Behavioral oracle for pop_scope. The source-grep above only proves a
# spelling; this proves teardown actually happens. `[Dict].pop()`
# mutates the receiver IN PLACE and returns the removed element, so
# `self.scopes.pop()` as a bare statement is correct and a write-back
# (`self.scopes = self.scopes.pop()`) would instead assign the removed
# scope over the array. Both halves are asserted here.
var env = Environment.new()
env.define("outer", Value.Int(1))

env.push_scope()
expect(env.scopes.len()).to_equal(2)
env.define("inner", Value.Int(2))
assert_true(env.lookup("inner").?)

env.pop_scope()
# depth returns to its prior value ...
expect(env.scopes.len()).to_equal(1)
# ... the popped scope's name no longer resolves ...
assert_false(env.lookup("inner").?)
# ... and the surviving outer scope is intact (catches a write-back
# that would clobber `scopes` with the removed element).
match env.lookup("outer"):
    case Some(v):
        match v:
            case Value.Int(value): expect(value).to_equal(1)
            case _: expect(false).to_equal(true)
    case _: expect(false).to_equal(true)
```

</details>

#### keeps the global scope when pop_scope underflows

- keeps the global scope when pop_scope underflows
   - Expected: env.scopes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the global scope when pop_scope underflows")
var env = Environment.new()
env.define("only", Value.Int(7))
env.pop_scope()
env.pop_scope()
expect(env.scopes.len()).to_equal(1)
assert_true(env.lookup("only").?)
```

</details>

#### snapshots visible closure locals with inner shadowing

- snapshots visible closure locals with inner shadowing


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("snapshots visible closure locals with inner shadowing")
var env = Environment.new()
var outer_scope: Dict<text, Value> = {}
outer_scope["outer"] = Value.Int(40)
var inner_scope: Dict<text, Value> = {}
inner_scope["outer"] = Value.Int(41)
inner_scope["inner"] = Value.Int(1)
env.scopes = [outer_scope, inner_scope]

val captured = env.snapshot_locals()
match captured["outer"]:
    case Value.Int(value): expect(value).to_equal(41)
    case _: expect(false).to_equal(true)
match captured["inner"]:
    case Value.Int(value): expect(value).to_equal(1)
    case _: expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/interpreter_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Interpreter Backend.
- Interpreter Backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55595ce2304d2ac350966affcdc03b7a1ae1fe93619902842c3081ee10080656`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55595ce2304d2ac350966affcdc03b7a1ae1fe93619902842c3081ee10080656`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55595ce2304d2ac350966affcdc03b7a1ae1fe93619902842c3081ee10080656`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/backend/interpreter_backend_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/interpreter_backend_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/backend/interpreter_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/interpreter_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/interpreter_backend_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/backend/interpreter_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/interpreter_backend_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/backend/interpreter_backend_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a backend port with stable metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/interpreter_backend_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an independent backend port per factory call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/interpreter_backend_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides a callable run function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
