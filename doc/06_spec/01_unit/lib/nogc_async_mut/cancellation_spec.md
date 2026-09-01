# Cancellation Specification

> Tests covering CancellationToken (real module, both constructors).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cancellation Specification

## Scenarios

### CancellationToken (real module, both constructors)

#### starts not cancelled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts not cancelled
   - Expected: t.is_cancelled() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts not cancelled")
val t = CancellationToken.new()
expect(t.is_cancelled()).to_equal(false)
```

</details>

#### cancel() flips is_cancelled() on the same token

- cancel() flips is_cancelled() on the same token
   - Expected: t.is_cancelled() is false
   - Expected: t.is_cancelled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancel() flips is_cancelled() on the same token")
var t = CancellationToken.new()
expect(t.is_cancelled()).to_equal(false)
t.cancel()
expect(t.is_cancelled()).to_equal(true)
```

</details>

#### token_new() free-function constructor behaves the same as .new()

- token_new() free-function constructor behaves the same as .new()
   - Expected: t.is_cancelled() is false
   - Expected: t.is_cancelled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("token_new() free-function constructor behaves the same as .new()")
var t = token_new()
expect(t.is_cancelled()).to_equal(false)
t.cancel()
expect(t.is_cancelled()).to_equal(true)
```

</details>

#### cancelling a parent is observed by an existing child

- cancelling a parent is observed by an existing child
   - Expected: child.is_cancelled() is false
   - Expected: child.is_cancelled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancelling a parent is observed by an existing child")
var parent = token_new()
var child = parent.child()
expect(child.is_cancelled()).to_equal(false)
parent.cancel()
expect(child.is_cancelled()).to_equal(true)
```

</details>

#### cancelling a child does not cancel its parent

- cancelling a child does not cancel its parent
   - Expected: child.is_cancelled() is true
   - Expected: parent.is_cancelled() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancelling a child does not cancel its parent")
var parent = token_new()
var child = parent.child()
child.cancel()
expect(child.is_cancelled()).to_equal(true)
expect(parent.is_cancelled()).to_equal(false)
```

</details>

#### cancelling one child does not affect an unrelated sibling

- cancelling one child does not affect an unrelated sibling
   - Expected: sib_a.is_cancelled() is true
   - Expected: sib_b.is_cancelled() is false
   - Expected: parent.is_cancelled() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancelling one child does not affect an unrelated sibling")
var parent = token_new()
var sib_a = parent.child()
var sib_b = parent.child()
sib_a.cancel()
expect(sib_a.is_cancelled()).to_equal(true)
expect(sib_b.is_cancelled()).to_equal(false)
expect(parent.is_cancelled()).to_equal(false)
```

</details>

#### allocates well past the old fixed 64-slot registry cap

- allocates well past the old fixed 64-slot registry cap
   - Expected: last.is_cancelled() is false
   - Expected: last.is_cancelled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates well past the old fixed 64-slot registry cap")
# The registry used to be a hardcoded 64-element array with no
# growth; the 65th token allocated in the process crashed on an
# out-of-bounds index. Confirms the growable-array fix.
var i = 0
var last = token_new()
while i < 200:
    last = token_new()
    i = i + 1
expect(last.is_cancelled()).to_equal(false)
last.cancel()
expect(last.is_cancelled()).to_equal(true)
```

</details>

#### guard_future() reflects cancellation state

- guard_future() reflects cancellation state
   - Expected: before.is_ready() is false
   - Expected: after.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard_future() reflects cancellation state")
var t = token_new()
val before = t.guard_future()
expect(before.is_ready()).to_equal(false)
t.cancel()
val after = t.guard_future()
expect(after.is_ready()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/cancellation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CancellationToken (real module, both constructors).
- CancellationToken (real module, both constructors)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `29b768dacd195e203ca41e63489f6838f5f56a704bc14974008fbdcd7ae05ddb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29b768dacd195e203ca41e63489f6838f5f56a704bc14974008fbdcd7ae05ddb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29b768dacd195e203ca41e63489f6838f5f56a704bc14974008fbdcd7ae05ddb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/cancellation_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/cancellation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/cancellation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/cancellation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/cancellation_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts not cancelled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/cancellation_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cancel() flips is_cancelled() on the same token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/cancellation_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'token_new() free-function constructor behaves the same as .new()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
