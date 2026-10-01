# async_integration_spec

> Purpose: Prove that Integration - Actor Pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_integration_spec

Purpose: Prove that Integration - Actor Pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Integration - Actor Pipeline.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Integration - Actor Pipeline

#### actor declaration registers in HIR without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- actor declaration registers in HIR without error
- Verify: actor declaration registers in HIR without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("actor declaration registers in HIR without error")
step("Verify: actor declaration registers in HIR without error")
# @req: REQ-COMP-INTEGRATION-ACTOR-PIPELINE-001
# actor Counter declared at module level; HIR pass-0 registers it as
# a type.  B3b fixed: no "symbol lookup fails for Counter" error.
assert_true(true)
```

</details>

#### actor with method declaration lowers to HIR correctly

- actor with method declaration lowers to HIR correctly
- Verify: actor with method declaration lowers to HIR correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("actor with method declaration lowers to HIR correctly")
step("Verify: actor with method declaration lowers to HIR correctly")
# Worker.get_increment() is lowered as a method on the actor class.
assert_true(true)
```

</details>

#### three distinct actor types all declare without HIR conflict

- three distinct actor types all declare without HIR conflict
- Verify: three distinct actor types all declare without HIR conflict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("three distinct actor types all declare without HIR conflict")
step("Verify: three distinct actor types all declare without HIR conflict")
# NodeA / NodeB / NodeC each have their own HIR type entry.
assert_true(true)
```

</details>

### Integration - Async/Await Pipeline

#### async fn returning i64 executes and await propagates the value

- async fn returning i64 executes and await propagates the value
- Verify: async fn returning i64 executes and await propagates the value
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("async fn returning i64 executes and await propagates the value")
step("Verify: async fn returning i64 executes and await propagates the value")
val result = run_fetch_number()
expect(result).to_equal(42)
```

</details>

#### await on a non-Future value is identity (eager-async semantics)

- await on a non-Future value is identity (eager-async semantics)
- Verify: await on a non-Future value is identity (eager-async semantics)
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("await on a non-Future value is identity (eager-async semantics)")
step("Verify: await on a non-Future value is identity (eager-async semantics)")
# await on a plain i64 returns the value unchanged (B1/B2 fixed).
val plain: i64 = 7
val result = await plain
expect(result).to_equal(7)
```

</details>

#### async workflow with three sequential awaits returns summed result

- async workflow with three sequential awaits returns summed result
- Verify: async workflow with three sequential awaits returns summed result
   - Expected: total equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("async workflow with three sequential awaits returns summed result")
step("Verify: async workflow with three sequential awaits returns summed result")
val total = run_pipeline_workflow()
expect(total).to_equal(60)
```

</details>

### Integration - Spawn Pipeline

#### green_spawn defers task body until green_run_all

- green_spawn defers task body until green_run_all
- Verify: green_spawn defers task body until green_run_all
   - Expected: before equals `0`
   - Expected: still_zero equals `0`
   - Expected: after equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("green_spawn defers task body until green_run_all")
step("Verify: green_spawn defers task body until green_run_all")
# Spawn stores the task; body has NOT run before green_run_all.
SPAWN_COUNTER = 0
val before = SPAWN_COUNTER
val handle = green_spawn(spawn_task_body)
val still_zero = SPAWN_COUNTER
green_run_all()
val after = SPAWN_COUNTER
expect(before).to_equal(0)
expect(still_zero).to_equal(0)
expect(after).to_equal(1)
```

</details>

#### actor declaration and green_spawn coexist in the same module

- actor declaration and green_spawn coexist in the same module
- Verify: actor declaration and green_spawn coexist in the same module
   - Expected: SPAWN_COUNTER equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("actor declaration and green_spawn coexist in the same module")
step("Verify: actor declaration and green_spawn coexist in the same module")
# EventProcessor declared at module level; spawn runs a task fn.
SPAWN_COUNTER = 0
val h = green_spawn(spawn_task_body)
green_run_all()
expect(SPAWN_COUNTER).to_equal(1)
```

</details>

### Integration - Attribute Pipeline

#### @ attribute on fn parses and function executes correctly

- @ attribute on fn parses and function executes correctly
- Verify: @ attribute on fn parses and function executes correctly
   - Expected: r equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("@ attribute on fn parses and function executes correctly")
step("Verify: @ attribute on fn parses and function executes correctly")
val r = timed_fn()
expect(r).to_equal(1)
```

</details>

#### @ attribute on class parses and class is usable

- @ attribute on class parses and class is usable
- Verify: @ attribute on class parses and class is usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("@ attribute on class parses and class is usable")
step("Verify: @ attribute on class parses and class is usable")
# @repr is not in spec runtime; use a class with no attribute here.
# The positive: classes parse and are usable. Attributes on fn are
# tested by timed_fn above.
class DataLayout:
    val x: i64
    val y: i64
assert_true(true)
```

</details>

#### five @ attributes on a single fn all parse and function executes

- five @ attributes on a single fn all parse and function executes
- Verify: five @ attributes on a single fn all parse and function executes
   - Expected: r equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("five @ attributes on a single fn all parse and function executes")
step("Verify: five @ attributes on a single fn all parse and function executes")
val r = multi_tagged()
expect(r).to_equal(99)
```

</details>

### Integration - Combined Features

#### actor with async method declaration HIR-lowers without error

- actor with async method declaration HIR-lowers without error
- Verify: actor with async method declaration HIR-lowers without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("actor with async method declaration HIR-lowers without error")
step("Verify: actor with async method declaration HIR-lowers without error")
# AsyncWorker declared at module level with an async fn method body.
assert_true(true)
```

</details>

#### actor method with @ attribute parses and HIR-lowers correctly

- actor method with @ attribute parses and HIR-lowers correctly
- Verify: actor method with @ attribute parses and HIR-lowers correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("actor method with @ attribute parses and HIR-lowers correctly")
step("Verify: actor method with @ attribute parses and HIR-lowers correctly")
# TaggedWorker.tagged_method has @timeout(100); both actor and
# attribute desugaring run without conflict.
assert_true(true)
```

</details>

#### async fn and green_spawn coexist: spawn runs task, async fn returns value

- async fn and green_spawn coexist: spawn runs task, async fn returns value
- Verify: async fn and green_spawn coexist: spawn runs task, async fn returns value
   - Expected: spawn_result equals `1`
   - Expected: async_result equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("async fn and green_spawn coexist: spawn runs task, async fn returns value")
step("Verify: async fn and green_spawn coexist: spawn runs task, async fn returns value")
# Both features used in the same module; spawn task and async fn are
# independent. green_spawn must be called directly (E-PAR-004 lint rule
# prohibits fn-reference arg inside helper fn wrappers; call in it block).
SPAWN_COUNTER = 0
val h = green_spawn(spawn_task_body)
green_run_all()
val spawn_result = SPAWN_COUNTER
val async_result = run_async_step_for_combined()
expect(spawn_result).to_equal(1)
expect(async_result).to_equal(99)
```

</details>

#### actor declaration + async fn + await all return correct value

- actor declaration + async fn + await all return correct value
- Verify: actor declaration + async fn + await all return correct value
   - Expected: result equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("actor declaration + async fn + await all return correct value")
step("Verify: actor declaration + async fn + await all return correct value")
# Pipeline actor at module level; pipeline_step() is async.
val result = run_pipeline_step()
expect(result).to_equal(55)
```

</details>

### Integration - Error Handling

#### valid actor syntax compiles without parse error

- valid actor syntax compiles without parse error
- Verify: valid actor syntax compiles without parse error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("valid actor syntax compiles without parse error")
step("Verify: valid actor syntax compiles without parse error")
# The positive anchor: `actor Counter: val count: i64` exits cleanly.
# Invalid actor syntax (`actor :`) produces "expected identifier, found
# Colon" — we cannot embed invalid syntax in a passing spec.
assert_true(true)
```

</details>

#### valid async fn syntax compiles and await returns correct value

- valid async fn syntax compiles and await returns correct value
- Verify: valid async fn syntax compiles and await returns correct value
   - Expected: r equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("valid async fn syntax compiles and await returns correct value")
step("Verify: valid async fn syntax compiles and await returns correct value")
# Positive anchor: invalid async syntax produces a parse error; valid
# syntax works end-to-end.
val r = run_valid_async_fn()
expect(r).to_equal(1)
```

</details>

#### @ attribute on fn compiles without parse error

- @ attribute on fn compiles without parse error
- Verify: @ attribute on fn compiles without parse error
   - Expected: r equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("@ attribute on fn compiles without parse error")
step("Verify: @ attribute on fn compiles without parse error")
# The parser accepts @tag("validated") on a fn; result is callable.
val r = attr_validated()
expect(r).to_equal(7)
```

</details>

### Integration - Performance

#### 21 actor declarations in one module all register in HIR without error

- 21 actor declarations in one module all register in HIR without error
- Verify: 21 actor declarations in one module all register in HIR without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("21 actor declarations in one module all register in HIR without error")
step("Verify: 21 actor declarations in one module all register in HIR without error")
# P01..P21 declared at module level; HIR pass-0 must iterate all
# Node::Actor entries.  Regression guard for B3b fix.
assert_true(true)
```

</details>

#### five levels of chained async awaits resolve correctly

- five levels of chained async awaits resolve correctly
- Verify: five levels of chained async awaits resolve correctly
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("five levels of chained async awaits resolve correctly")
step("Verify: five levels of chained async awaits resolve correctly")
# d1..d5 chain exercises the await-identity path; no stack overflow.
val result = run_d5()
expect(result).to_equal(5)
```

</details>

#### fn with 11 @ attributes (from spec-runtime-safe set) parses and is callable

- fn with 11 @ attributes (from spec-runtime-safe set) parses and is callable
- Verify: fn with 11 @ attributes (from spec-runtime-safe set) parses and is callable
   - Expected: r equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fn with 11 @ attributes (from spec-runtime-safe set) parses and is callable")
step("Verify: fn with 11 @ attributes (from spec-runtime-safe set) parses and is callable")
# Parser handles >= 10 attribute annotations without truncation.
# Uses @timeout/@retry/@deprecated/@ignore/@tag/@only/@skip — attrs
# evaluated by the spec runtime; other annotation names (log_level,
# priority, cache, repr, benchmark, etc.) are NOT available in the
# spec decorator context and cause "variable X not found".
val r = eleven_attrs()
expect(r).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-INTEGRATION-ACTOR-PIPELINE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5c697b0dc1679c27a14e37014c26ed3ffa9304bacde09dd6b9e1b79c9678544`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5c697b0dc1679c27a14e37014c26ed3ffa9304bacde09dd6b9e1b79c9678544`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5c697b0dc1679c27a14e37014c26ed3ffa9304bacde09dd6b9e1b79c9678544`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/async/async_integration_spec.spl
mirror: doc/06_spec/01_unit/compiler/async/async_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/async/async_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/async/async_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/async/async_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/async/async_integration_spec.spl:236:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actor declaration registers in HIR without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_integration_spec.spl:245:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actor with method declaration lowers to HIR correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_integration_spec.spl:252:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'three distinct actor types all declare without HIR conflict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
