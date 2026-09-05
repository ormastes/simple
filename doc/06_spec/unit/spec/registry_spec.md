# registry_spec

> Unit tests for the BDD Registry module.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# registry_spec

Unit tests for the BDD Registry module.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/spec/registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the BDD Registry module.

This test file verifies the core components of the BDD test registry system:
- Example: Test case representation with skip, slow, timeout, and tag support
- ExampleGroup: Hierarchical grouping of test cases with hooks
- Registry functions: Global registration and retrieval of test groups

Uses mock implementations to isolate registry logic from the actual test framework.

## Scenarios

### BDD Registry

#### Example

#### creates a new example with description and block

- creates a new example with description and block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a new example with description and block")
val example = Example.create("test description", \: ())
expect example.description == "test description"
expect example.is_skipped == false
expect example.tags.len() == 0
```

</details>

#### can be marked as skipped

- can be marked as skipped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be marked as skipped")
val example = Example.create("test", \: ()).skip()
expect example.is_skipped == true
expect example.is_pending() == true
```

</details>

#### can be marked as slow

- can be marked as slow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be marked as slow")
val example = Example.create("test", \: ()).slow()
expect example.has_tag("slow") == true
```

</details>

#### can have a timeout set

- can have a timeout set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can have a timeout set")
val example = Example.create("test", \: ()).with_timeout(30)
match example.timeout_seconds:
    case Some(timeout): expect timeout == 30
    case nil: expect false
```

</details>

#### can have tags added

- can have tags added


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can have tags added")
val example = Example.create("test", \: ()).with_tag("integration").with_tag("database")
expect example.has_tag("integration") == true
expect example.has_tag("database") == true
expect example.has_tag("nonexistent") == false
```

</details>

#### should_run returns false for skipped examples

- should_run returns false for skipped examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should_run returns false for skipped examples")
val example = Example.create("test", \: ()).skip()
expect example.should_run(true) == false
```

</details>

#### should_run returns false for slow examples when run_slow is false

- should_run returns false for slow examples when run_slow is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should_run returns false for slow examples when run_slow is false")
val example = Example.create("test", \: ()).slow()
expect example.should_run(false) == false
```

</details>

#### should_run returns true for slow examples when run_slow is true

- should_run returns true for slow examples when run_slow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should_run returns true for slow examples when run_slow is true")
val example = Example.create("test", \: ()).slow()
expect example.should_run(true) == true
```

</details>

#### ExampleGroup

#### creates a new group with description

- creates a new group with description


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a new group with description")
val group = ExampleGroup.create("MyClass", nil)
expect group.description == "MyClass"
expect group.children.len() == 0
expect group.test_examples.len() == 0
```

</details>

#### can add examples

- can add examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can add examples")
val group = ExampleGroup.create("Test", nil)
val example = Example.create("does something", \: ())
group.add_example(example)
expect group.test_examples.len() == 1
expect group.test_examples[0].description == "does something"
```

</details>

#### full_description returns description for top-level group

- full_description returns description for top-level group


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full_description returns description for top-level group")
val group = ExampleGroup.create("Calculator", nil)
expect group.full_description() == "Calculator"
```

</details>

#### example_count returns count of direct examples

- example_count returns count of direct examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("example_count returns count of direct examples")
val group = ExampleGroup.create("Test", nil)
group.add_example(Example.create("test 1", \: ()))
group.add_example(Example.create("test 2", \: ()))
expect group.example_count() == 2
```

</details>

#### Registry - Groups

#### can register example groups

- can register example groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register example groups")
reset_registry()
val group = ExampleGroup.create("Test", nil)
register_group(group)
val groups = get_all_groups()
expect groups.len() == 1
expect groups[0].description == "Test"
```

</details>

#### can clear all groups

- can clear all groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can clear all groups")
reset_registry()
register_group(ExampleGroup.create("Test", nil))
clear_groups()
expect get_all_groups().len() == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `ae5c3b0b011f8316d4277045f04eefb266b78cd9b044ad549e47359ce2ff15be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae5c3b0b011f8316d4277045f04eefb266b78cd9b044ad549e47359ce2ff15be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae5c3b0b011f8316d4277045f04eefb266b78cd9b044ad549e47359ce2ff15be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/spec/registry_spec.spl
mirror: doc/06_spec/unit/spec/registry_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/spec/registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/spec/registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/spec/registry_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a new example with description and block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/registry_spec.spl:121:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be marked as skipped' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/registry_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can be marked as skipped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/registry_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be marked as slow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/registry_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can be marked as slow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/registry_spec.spl:134:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can have a timeout set' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/registry_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can have tags added' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/registry_spec.spl:177:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can add examples' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/registry_spec.spl:201:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can register example groups' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
