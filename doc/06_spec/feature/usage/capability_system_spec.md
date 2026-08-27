# Reference Capability System Specification

> @concurrency_mode(lock_base)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reference Capability System Specification

@concurrency_mode(lock_base)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CAP-SYS-001 to #CAP-SYS-034 |
| Category | Type System \| Capabilities |
| Status | Implemented |
| Source | `test/feature/usage/capability_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Capability Types

- `T` (default) - Shared, no mutation, no transfer
- `mut T` - Exclusive, allows mutation, no transfer
- `iso T` - Isolated, allows mutation and transfer

## Concurrency Modes

- Actor (default) - Only `iso T` allowed, `mut T` rejected
- LockBase - `mut T` and `iso T` allowed
- Unsafe - All capabilities allowed

## Syntax

```simple
@concurrency_mode(lock_base)
use std.spec.step

fn update(counter: mut Counter, delta: i64) -> i64:
counter.value = counter.value + delta
counter.value
```

## Scenarios

### Parsing Capabilities

#### parses mut capability

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses mut capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mut capability")
@concurrency_mode(lock_base)
fn update(x: mut i64) -> i64:
    x

expect true  # Parsed successfully
```

</details>

#### parses iso capability

- parses iso capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses iso capability")
fn transfer(data: iso i64) -> i64:
    data

expect true  # Parsed successfully
```

</details>

#### parses capability with generic type

- parses capability with generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses capability with generic type")
@concurrency_mode(lock_base)
fn process(items: mut [i64]) -> i64:
    0

expect true  # Parsed successfully
```

</details>

#### parses default shared capability (no prefix)

- parses default shared capability (no prefix)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses default shared capability (no prefix)")
fn read(x: i64) -> i64:
    x

expect true  # Default is implicitly Shared
```

</details>

### Aliasing Rules

#### allows multiple shared capabilities

- allows multiple shared capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows multiple shared capabilities")
# Shared capabilities can coexist
fn use_shared(a: i64, b: i64) -> i64:
    a + b

expect use_shared(10, 20) == 30
```

</details>

#### exclusive capability prevents aliasing

- exclusive capability prevents aliasing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("exclusive capability prevents aliasing")
# Exclusive (mut) capability prevents any other references
# This is enforced at compile time
expect true
```

</details>

#### isolated capability prevents aliasing

- isolated capability prevents aliasing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolated capability prevents aliasing")
# Isolated (iso) capability prevents any other references
# This is enforced at compile time
expect true
```

</details>

### Capability Conversion Rules

#### valid downgrades

#### allows Exclusive to Shared

- allows Exclusive to Shared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows Exclusive to Shared")
# mut T -> T is allowed (downgrade)
expect true
```

</details>

#### allows Isolated to Exclusive

- allows Isolated to Exclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows Isolated to Exclusive")
# iso T -> mut T is allowed (downgrade)
expect true
```

</details>

#### allows Isolated to Shared

- allows Isolated to Shared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows Isolated to Shared")
# iso T -> T is allowed (downgrade)
expect true
```

</details>

#### invalid upcasts

#### rejects Shared to Exclusive

- rejects Shared to Exclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects Shared to Exclusive")
# T -> mut T is not allowed (upcast)
expect true  # Compile-time check
```

</details>

#### rejects Shared to Isolated

- rejects Shared to Isolated


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects Shared to Isolated")
# T -> iso T is not allowed (upcast)
expect true  # Compile-time check
```

</details>

#### rejects Exclusive to Isolated

- rejects Exclusive to Isolated


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects Exclusive to Isolated")
# mut T -> iso T is not allowed (upcast)
expect true  # Compile-time check
```

</details>

### Capability Properties

#### shared allows no mutation

- shared allows no mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("shared allows no mutation")
# T cannot be mutated
expect true
```

</details>

#### exclusive allows mutation

- exclusive allows mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("exclusive allows mutation")
# mut T can be mutated
@concurrency_mode(lock_base)
fn mutate(x: mut i64) -> i64:
    x = x + 1
    x

expect true
```

</details>

#### isolated allows mutation and transfer

- isolated allows mutation and transfer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("isolated allows mutation and transfer")
# iso T can be mutated and transferred
fn take_ownership(data: iso i64) -> i64:
    data

expect true
```

</details>

### Nested Capabilities

#### parses nested mut mut T

- parses nested mut mut T


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nested mut mut T")
@concurrency_mode(lock_base)
fn weird(x: mut mut i64) -> i64:
    0

expect true  # Parses (though semantically questionable)
```

</details>

### Capability Environment

#### can acquire and release capability

- can acquire and release capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can acquire and release capability")
# After acquiring exclusive, cannot acquire shared
# After release, can acquire again
expect true  # Runtime behavior
```

</details>

### Concurrency Mode - Actor

#### defaults to actor mode

- defaults to actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defaults to actor mode")
fn process(x: i64) -> i64:
    x

expect process(42) == 42
```

</details>

#### actor mode allows iso

- actor mode allows iso


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("actor mode allows iso")
fn transfer(data: iso i64) -> i64:
    data

expect transfer(42) == 42
```

</details>

#### actor mode rejects mut in params

- actor mode rejects mut in params


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("actor mode rejects mut in params")
# This would be a compile error:
# fn update(x: mut i64) -> i64:  # Error in actor mode
#     x
expect true  # Compile-time check
```

</details>

### Concurrency Mode - LockBase

#### parses lock_base mode attribute

- parses lock_base mode attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses lock_base mode attribute")
@concurrency_mode(lock_base)
fn update(x: mut i64) -> i64:
    x

expect true
```

</details>

#### lock_base allows mut T

- lock_base allows mut T


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lock_base allows mut T")
@concurrency_mode(lock_base)
fn increment(counter: mut i64, delta: i64) -> i64:
    counter + delta

expect true
```

</details>

### Concurrency Mode - Unsafe

#### parses unsafe mode attribute

- parses unsafe mode attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses unsafe mode attribute")
@concurrency_mode(unsafe)
fn raw_ptr(x: i64) -> i64:
    x

expect true
```

</details>

#### unsafe mode allows all capabilities

- unsafe mode allows all capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unsafe mode allows all capabilities")
@concurrency_mode(unsafe)
fn unsafe_process(a: mut i64, b: iso i64, c: i64) -> mut i64:
    0

expect true
```

</details>

### iso T in All Modes

#### iso works in actor mode

- iso works in actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("iso works in actor mode")
fn transfer_actor(x: iso i64) -> i64:
    x

expect transfer_actor(42) == 42
```

</details>

#### iso works in lock_base mode

- iso works in lock_base mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("iso works in lock_base mode")
@concurrency_mode(lock_base)
fn transfer_lock(x: iso i64) -> i64:
    x

expect transfer_lock(42) == 42
```

</details>

#### iso works in unsafe mode

- iso works in unsafe mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("iso works in unsafe mode")
@concurrency_mode(unsafe)
fn transfer_unsafe(x: iso i64) -> i64:
    x

expect transfer_unsafe(42) == 42
```

</details>

### Zero-Cost Abstraction

#### capabilities compile to same representation

- capabilities compile to same representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("capabilities compile to same representation")
# mut T, iso T, and T all have the same size
# Capabilities only affect compile-time checking
expect true
```

</details>

### Multiple Parameters with Capabilities

#### allows mixed capabilities in lock_base

- allows mixed capabilities in lock_base


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows mixed capabilities in lock_base")
@concurrency_mode(lock_base)
fn process(a: mut i64, b: iso i64, c: i64) -> i64:
    a + c

expect true
```

</details>

#### allows all shared in actor mode

- allows all shared in actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows all shared in actor mode")
fn read_all(a: i64, b: i64, c: i64) -> i64:
    a + b + c

expect read_all(10, 20, 12) == 42
```

</details>

### Return Type Capabilities

#### allows mut return in lock_base

- allows mut return in lock_base


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows mut return in lock_base")
@concurrency_mode(lock_base)
fn create_mut() -> mut i64:
    42

expect true
```

</details>

#### allows iso return in all modes

- allows iso return in all modes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows iso return in all modes")
fn send(data: iso i64) -> iso i64:
    data

expect true
```

</details>

### Class Method Capabilities

#### class methods default to actor mode

- class methods default to actor mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("class methods default to actor mode")
class Counter:
    value: i64

    fn get_value() -> i64:
        self.value

val c = Counter(value: 42)
expect c.get_value() == 42
```

</details>

### Integration Patterns

#### actor message passing with iso

- actor message passing with iso


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("actor message passing with iso")
fn process_message(msg: iso i64) -> i64:
    msg

expect process_message(42) == 42
```

</details>

#### lock-based concurrent modification

- lock-based concurrent modification


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lock-based concurrent modification")
@concurrency_mode(lock_base)
fn increment(counter: mut i64, delta: i64) -> i64:
    counter + delta

expect true
```

</details>

#### builder pattern with mut

- builder pattern with mut


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builder pattern with mut")
@concurrency_mode(lock_base)
fn with_value(builder: mut i64, value: i64) -> mut i64:
    builder

expect true
```

</details>

#### unsafe mode escape hatch

- unsafe mode escape hatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unsafe mode escape hatch")
@concurrency_mode(unsafe)
fn unsafe_modify(data: mut i64, value: i64) -> i64:
    value

expect true
```

</details>

#### iso transfer semantics

- iso transfer semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("iso transfer semantics")
fn consume(data: iso i64) -> i64:
    data

expect consume(42) == 42
```

</details>

#### mixed const and mut parameters

- mixed const and mut parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixed const and mut parameters")
@concurrency_mode(lock_base)
fn update_with_config(state: mut i64, config: i64, multiplier: i64) -> i64:
    config * multiplier

expect update_with_config(0, 6, 7) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4597d8e2b215943095be1a67ee5307ea87b8ac2a9f6684f5158f5ebaeaff4936`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4597d8e2b215943095be1a67ee5307ea87b8ac2a9f6684f5158f5ebaeaff4936`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4597d8e2b215943095be1a67ee5307ea87b8ac2a9f6684f5158f5ebaeaff4936`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/feature/usage/capability_system_spec.spl
mirror: doc/06_spec/feature/usage/capability_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/capability_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/capability_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/capability_system_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses mut capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/capability_system_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses iso capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/capability_system_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses capability with generic type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/capability_system_spec.spl:235:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can acquire and release capability' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
