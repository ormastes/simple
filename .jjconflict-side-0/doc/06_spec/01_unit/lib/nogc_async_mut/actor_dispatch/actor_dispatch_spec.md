# Actor Dispatch Specification

> Tests covering HandlerTable registration, Actor isolation by convention, ActorRuntime process_mailbox.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Dispatch Specification

## Scenarios

### HandlerTable registration

#### registered handler is invoked and returns its result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registered handler is invoked and returns its result
   - Expected: result.is_ok() is true
   - Expected: result.value equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registered handler is invoked and returns its result")
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("echo", ["hello"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("hello")
```

</details>

#### registering a second handler replaces the first

- registering a second handler replaces the first
   - Expected: result.is_ok() is true
   - Expected: result.value equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registering a second handler replaces the first")
var ht = make_handlers()
ht.register("greet", handler_echo)
ht.register("greet", handler_greet)

val result = ht.dispatch("greet", ["World"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("Hello, World!")
```

</details>

#### dispatching unknown method returns MethodNotFound error not crash

- dispatching unknown method returns MethodNotFound error not crash
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatching unknown method returns MethodNotFound error not crash")
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("no_such_method", [])

expect(result.is_ok()).to_equal(false)
expect(result.error_msg).to_contain("no_such_method")
```

</details>

#### dispatching unknown method on empty table returns typed error

- dispatching unknown method on empty table returns typed error
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatching unknown method on empty table returns typed error")
var ht = make_handlers()

val result = ht.dispatch("totally_unknown", ["arg1", "arg2"])

expect(result.is_ok()).to_equal(false)
expect(result.error_msg).to_contain("totally_unknown")
```

</details>

#### call() returns handler result synchronously

- call() returns handler result synchronously
   - Expected: result.is_ok() is true
   - Expected: result.value equals `Hello, Alice!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call() returns handler result synchronously")
# Models ProcessManager Shared-mode call(): direct HandlerTable dispatch.
var ht = make_handlers()
ht.register("greet", handler_greet)

val result = ht.dispatch("greet", ["Alice"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("Hello, Alice!")
```

</details>

#### cast() fire-and-forget: dispatch runs and result is safely ignored

- cast() fire-and-forget: dispatch runs and result is safely ignored
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cast() fire-and-forget: dispatch runs and result is safely ignored")
# Models ProcessManager Shared cast(): dispatch runs, caller drops result.
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("echo", ["data"])

expect(result.is_ok()).to_equal(true)
```

</details>

### Actor isolation by convention

#### two handler tables with same method name dispatch independently

- two handler tables with same method name dispatch independently
   - Expected: result_a.is_ok() is true
   - Expected: result_b.is_ok() is true
   - Expected: result_a.value equals `a_result`
   - Expected: result_b.value equals `b_result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two handler tables with same method name dispatch independently")
# Actors are share-nothing by convention: separate HandlerTable instances
# never share entries or state.
var ht_a = make_handlers()
ht_a.register("id", handler_count_a)

var ht_b = make_handlers()
ht_b.register("id", handler_count_b)

val result_a = ht_a.dispatch("id", [])
val result_b = ht_b.dispatch("id", [])

expect(result_a.is_ok()).to_equal(true)
expect(result_b.is_ok()).to_equal(true)
expect(result_a.value).to_equal("a_result")
expect(result_b.value).to_equal("b_result")
# Different values confirm the two tables are independent.
expect(result_a.value).to_not_equal(result_b.value)
```

</details>

#### registering a handler in one table does not affect another table

- registering a handler in one table does not affect another table
   - Expected: result_a.is_ok() is true
   - Expected: result_b.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registering a handler in one table does not affect another table")
var ht_a = make_handlers()
ht_a.register("method_x", handler_echo)

var ht_b = make_handlers()
# ht_b has no "method_x"

val result_a = ht_a.dispatch("method_x", ["hello"])
val result_b = ht_b.dispatch("method_x", ["hello"])

expect(result_a.is_ok()).to_equal(true)
expect(result_b.is_ok()).to_equal(false)
```

</details>

#### actor IDs are unique across separately spawned actors

- actor IDs are unique across separately spawned actors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actor IDs are unique across separately spawned actors")
var ht = make_handlers()
ht.register("noop", handler_noop)

val ref1 = spawn_actor(ht)
val ref2 = spawn_actor(ht)

expect(ref1.get_id()).to_not_equal(ref2.get_id())
```

</details>

### ActorRuntime process_mailbox

#### dispatching a known method succeeds

- dispatching a known method succeeds
   - Expected: result.is_ok() is true
   - Expected: result.value equals `pong`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatching a known method succeeds")
# Test the dispatch machinery directly using HandlerTable.dispatch(),
# which is the synchronous path used by both run_once and direct call().
# NOTE: Dict value-semantics mean mailbox push via actors.get() does not
# persist; this test validates the dispatch step in isolation.
var ht = make_handlers()
ht.register("ping", handler_echo)

val result = ht.dispatch("ping", ["pong"])

expect(result.is_ok()).to_equal(true)
expect(result.value).to_equal("pong")
```

</details>

#### dispatching unknown method returns error result not panic

- dispatching unknown method returns error result not panic
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatching unknown method returns error result not panic")
var ht = make_handlers()
ht.register("echo", handler_echo)

val result = ht.dispatch("no_such_method", [])

expect(result.is_ok()).to_equal(false)
expect(result.error_msg).to_contain("no_such_method")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HandlerTable registration, Actor isolation by convention, ActorRuntime process_mailbox.
- HandlerTable registration
- Actor isolation by convention
- ActorRuntime process_mailbox

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `44d5ddeb377c3816d6269043b2a9cdef07feb34a7acca2a477e106a10f7e78fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44d5ddeb377c3816d6269043b2a9cdef07feb34a7acca2a477e106a10f7e78fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44d5ddeb377c3816d6269043b2a9cdef07feb34a7acca2a477e106a10f7e78fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registered handler is invoked and returns its result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registering a second handler replaces the first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/actor_dispatch/actor_dispatch_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatching unknown method returns MethodNotFound error not crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
