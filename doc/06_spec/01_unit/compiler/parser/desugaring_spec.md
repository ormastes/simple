# desugaring_spec

> Purpose and audience: compiler engineers on the frontend team who rely on

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# desugaring_spec

Purpose and audience: compiler engineers on the frontend team who rely on

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/desugaring_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: compiler engineers on the frontend team who rely on
    the desugaring pass lowering async/await and actor syntax into core forms
    (Future-returning functions, block_on calls, classes with actor semantics)
    without changing observable program behaviour. Each scenario runs a real
    fixture through the deployed compiler binary and asserts its output.

## Scenarios

### Desugaring

#### an async function with an explicit return type awaits to its value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compile and run a fixture that awaits a typed async function
- the awaited value is the async body's result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture that awaits a typed async function")
val out = compile_source("async_explicit", ASYNC_EXPLICIT_SOURCE)

step("the awaited value is the async body's result")
expect(out).to_contain("await 42")
```

</details>

#### an async function without a return type is awaitable and runs its body

- compile and run a fixture that awaits an untyped async function
- the body's side effect happens exactly once, then execution continues


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture that awaits an untyped async function")
val out = compile_source("async_unit", ASYNC_UNIT_SOURCE)

step("the body's side effect happens exactly once, then execution continues")
expect(out).to_contain("side effect ran")
expect(out).to_contain("after await")
```

</details>

#### awaiting inside another async function composes results

- compile and run a fixture with a nested await
- the inner await resolves first and feeds the outer body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture with a nested await")
val out = compile_source("nested", NESTED_AWAIT_SOURCE)

step("the inner await resolves first and feeds the outer body")
expect(out).to_contain("nested 15")
```

</details>

#### several awaits in one body each resolve to their own value

- compile and run a fixture with two awaits in one body
- both awaited values contribute to the printed sum 1 + 2 = 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture with two awaits in one body")
val out = compile_source("two_awaits", TWO_AWAITS_SOURCE)

step("both awaited values contribute to the printed sum 1 + 2 = 3")
expect(out).to_contain("sum 3")
```

</details>

#### an actor declaration desugars and spawns as an instance

- compile and run a fixture that spawns a field-only actor
- the program runs to completion after the spawn


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture that spawns a field-only actor")
val out = compile_source("actor_spawn", ACTOR_SPAWN_SOURCE)

step("the program runs to completion after the spawn")
expect(out).to_contain("spawned")
```

</details>

#### a generic actor declaration is rejected up front, not silently mangled

- compile a fixture that declares actor Box<T> and spawns it
- the deployed parser has no generic-actor support (seed gap,
- recorded here as a fail-closed oracle: the program is refused
- with a parse error instead of desugaring to a wrong class)
   - Expected: out does not contain `generic spawned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile a fixture that declares actor Box<T> and spawns it")
val out = compile_source("generic_actor", GENERIC_ACTOR_SOURCE)

step("the deployed parser has no generic-actor support (seed gap,")
step("recorded here as a fail-closed oracle: the program is refused")
step("with a parse error instead of desugaring to a wrong class)")
expect(out).to_contain("parse:")
expect(out.contains("generic spawned")).to_equal(false)
```

</details>

#### a pub actor keeps its visibility through desugaring

- compile and run a fixture that spawns a pub actor
- the pub actor spawns without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture that spawns a pub actor")
val out = compile_source("pub_actor", PUB_ACTOR_SOURCE)

step("the pub actor spawns without error")
expect(out).to_contain("pub spawned")
```

</details>

#### an actor with methods desugars far enough to spawn

- compile and run a fixture whose actor declares a method
- the actor class is constructed by spawn; method invocation after
- spawn is not executable on the deployed seed and is tracked
- in the desugaring limitation note at the top of this spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile and run a fixture whose actor declares a method")
val out = compile_source("actor_methods", ACTOR_WITH_METHODS_SOURCE)

step("the actor class is constructed by spawn; method invocation after")
step("spawn is not executable on the deployed seed and is tracked")
step("in the desugaring limitation note at the top of this spec")
expect(out).to_contain("methods spawned")
```

</details>

#### await on a non-future value is rejected rather than silently passed

- compile a fixture that awaits a plain integer
- the compiler refuses the program instead of printing a value
   - Expected: out does not contain `await 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compile a fixture that awaits a plain integer")
val out = compile_source("await_error", AWAIT_ERROR_SOURCE)

step("the compiler refuses the program instead of printing a value")
expect(out.contains("await 5")).to_equal(false)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e0f5a8a15837d073eef9e049e71dcf2a2fbaffa3e2836bd4b87c686f25fcedc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e0f5a8a15837d073eef9e049e71dcf2a2fbaffa3e2836bd4b87c686f25fcedc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e0f5a8a15837d073eef9e049e71dcf2a2fbaffa3e2836bd4b87c686f25fcedc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/desugaring_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/desugaring_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/desugaring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/desugaring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/desugaring_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an async function with an explicit return type awaits to its value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/desugaring_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an async function without a return type is awaitable and runs its body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/desugaring_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'awaiting inside another async function composes results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
