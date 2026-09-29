# Mock Policy Execution Specification

> Tests covering Mock policy executor integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mock Policy Execution Specification

## Scenarios

### Mock policy executor integration

#### bans Mock.new, Spy.new, and Stub.new in system-test mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bans Mock.new, Spy.new, and Stub.new in system-test mode
   - Expected: results.total_count() equals `3`
   - Expected: results.failed_count() equals `3`
   - Expected: results.passed_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bans Mock.new, Spy.new, and Stub.new in system-test mode")
mock_policy_reset()

val group = ExampleGroup.new("system policy", nil).with_mock_mode(MockMode.Disabled)
group.add_example(Example.new("Mock.new is blocked", mock_block).system_test())
group.add_example(Example.new("Spy.new is blocked", spy_block).system_test())
group.add_example(Example.new("Stub.new is blocked", stub_block).system_test())

val results = execute_group(group)

expect(results.total_count()).to_equal(3)
expect(results.failed_count()).to_equal(3)
expect(results.passed_count()).to_equal(0)

mock_policy_reset()
```

</details>

#### keeps a system-test group banned while allowing an explicit unit-test override

- keeps a system-test group banned while allowing an explicit unit-test override
   - Expected: results.total_count() equals `2`
   - Expected: results.failed_count() equals `1`
   - Expected: results.passed_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps a system-test group banned while allowing an explicit unit-test override")
mock_policy_reset()

val parent = ExampleGroup.new("parent", nil).with_mock_mode(MockMode.Disabled)
val child = ExampleGroup.new("child", Some(parent))
parent.add_child(child)

child.add_example(Example.new("inherits disabled policy", mock_block).system_test())
child.add_example(Example.new("overrides to allow mocks", override_block).unit_test())

val results = execute_group(parent)

expect(results.total_count()).to_equal(2)
expect(results.failed_count()).to_equal(1)
expect(results.passed_count()).to_equal(1)

mock_policy_reset()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/spec/mock_policy_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mock policy executor integration.
- Mock policy executor integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ea90669f453cb22e2f7f64e3a13fa6041678a50f3c8e77d73bb61900ce30f2a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ea90669f453cb22e2f7f64e3a13fa6041678a50f3c8e77d73bb61900ce30f2a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ea90669f453cb22e2f7f64e3a13fa6041678a50f3c8e77d73bb61900ce30f2a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/spec/mock_policy_execution_spec.spl
mirror: doc/06_spec/integration/spec/mock_policy_execution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/spec/mock_policy_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/spec/mock_policy_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/spec/mock_policy_execution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/spec/mock_policy_execution_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bans Mock.new, Spy.new, and Stub.new in system-test mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/spec/mock_policy_execution_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a system-test group banned while allowing an explicit unit-test override' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
