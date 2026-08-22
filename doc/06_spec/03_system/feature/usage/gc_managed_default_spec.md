# gc_managed_default_spec

> Purpose: the default heap-management behavior (unqualified objects, containers, references) asserted in this spec. Audience: engineers reading this spec to confirm the runtime's default memory behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gc_managed_default_spec

Purpose: the default heap-management behavior (unqualified objects, containers, references) asserted in this spec. Audience: engineers reading this spec to confirm the runtime's default memory behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/03_system/feature/usage/gc_managed_default_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the default heap-management behavior (unqualified objects, containers, references) asserted in this spec. Audience: engineers reading this spec to confirm the runtime's default memory behavior still holds.

## Operator workflow

1. Run `bin/simple test test/03_system/feature/usage/gc_managed_default_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers observable default-allocation behavior on the current runtime (value semantics with copy-on-write). Explicit collection/finalizer timing is out of scope.

## Scenarios

### Garbage-Collected Memory Management as the Default Strategy

#### Default allocation

#### allocates unqualified class instances without an explicit memory annotation

- Construct GcBox with no capability annotation and read it back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Construct GcBox with no capability annotation and read it back")
val b = GcBox(payload: 41)
assert_equal(b.payload, 41)
```

</details>

#### allocates lists of heap objects by default

- Build a list of GcBox instances and reduce it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Build a list of GcBox instances and reduce it")
val boxes = [GcBox(payload: 1), GcBox(payload: 2), GcBox(payload: 3)]
assert_equal(box_sum(boxes), 6)
```

</details>

#### allocates dicts holding class instances by default

- Store GcBox instances in a dict and read one back


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Store GcBox instances in a dict and read one back")
val d = {"a": GcBox(payload: 7), "b": GcBox(payload: 9)}
match d.get("a"):
    case Some(box): assert_equal(box.payload, 7)
    case None: fail("key a missing")
```

</details>

#### Reference behavior

#### keeps an object usable through multiple references

- Alias a box, read through both names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Alias a box, read through both names")
val first = GcBox(payload: 5)
val second = first
assert_equal(second.payload + first.payload, 10)
```

</details>

#### never exposes use-after-free within a scope

- Overwrite a list slot and confirm survivors stay intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Overwrite a list slot and confirm survivors stay intact")
var items = [GcBox(payload: 10), GcBox(payload: 20)]
items[0] = GcBox(payload: 30)
assert_equal(box_sum(items), 50)
```

</details>

#### supports mutation of a mutable object

- Mutate a var-held box field and observe the new value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Mutate a var-held box field and observe the new value")
var box = GcBox(payload: 1)
box.payload = 12
assert_equal(box.payload, 12)
```

</details>

#### Memory pressure

#### survives allocating and discarding many short-lived objects

- Allocate 5000 boxes across 20 batches, keep batch sums


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Allocate 5000 boxes across 20 batches, keep batch sums")
var grand: i64 = 0
var batch: usize = 0
while batch < 20:
    var boxes: [GcBox] = []
    var i: usize = 0
    while i < 250:
        boxes.push(GcBox(payload: 2))
        i = i + 1
    grand = grand + box_sum(boxes)
    batch = batch + 1
assert_equal(grand, 10000)
```

</details>

#### keeps live objects correct while churn allocates around them

- Hold a live list while allocating throwaway batches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Hold a live list while allocating throwaway batches")
val live = [GcBox(payload: 100), GcBox(payload: 200)]
var churn: usize = 0
while churn < 100:
    val throwaway = [GcBox(payload: 1)]
    assert_equal(throwaway[0].payload, 1)
    churn = churn + 1
assert_equal(box_sum(live), 300)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b133ef2ef9be86702d8bc89166eb5f5792eb226e0e22117e79edee1b00544d75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b133ef2ef9be86702d8bc89166eb5f5792eb226e0e22117e79edee1b00544d75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b133ef2ef9be86702d8bc89166eb5f5792eb226e0e22117e79edee1b00544d75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/gc_managed_default_spec.spl
mirror: doc/06_spec/03_system/feature/usage/gc_managed_default_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/gc_managed_default_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/gc_managed_default_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/gc_managed_default_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates unqualified class instances without an explicit memory annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gc_managed_default_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates lists of heap objects by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gc_managed_default_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates dicts holding class instances by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
