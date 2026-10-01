# @req REQ-PREVENT-MOCK-1

> Prevention Mock Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-PREVENT-MOCK-1

Prevention Mock Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/testing/prevention_mock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Prevention Mock Specification

A prevention mock is the inverse of a normal expectation: it exists to FAIL a
test when a forbidden call path is taken (a real fs write in a pure test,
network I/O in a unit test, a deprecated API) instead of asserting that a
wanted call happened. `ForbiddenCallGuard` wraps a `MockFunction` with a
reason and a call budget (normally 0, "never call this"); `check_guards`
evaluates a list of guards and returns one human-readable failure message per
violated guard, naming both the mock and the reason.

This spec covers the per-test guard shape (`ForbiddenCallGuard.new`,
`ForbiddenCallGuard.at_most`) and, since the spec-DSL auto-check hook
(`prevent`/`prevent_file` in spec.spl) is a separate unit not landed here,
simulates file scope by calling `check_guards` after each of several
examples against one guard armed once — proving `check_guards` is safe to
call repeatedly without losing or resetting guard state on its own.

Feature IDs: Testing Infrastructure - Prevention Mocks
Category: Testing

## Scenarios

### prevention mocks

#### a prevention mock that is never called leaves the example green

- a prevention mock that is never called leaves the example green
- declare a prevention mock for the deprecated writer
- code under test never takes the forbidden path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a prevention mock that is never called leaves the example green")
step("declare a prevention mock for the deprecated writer")
val m = MockFunction.new("legacy_write")
val g = ForbiddenCallGuard.new(m, "legacy_write is deprecated; use write_v2")
step("code under test never takes the forbidden path")
val msgs = check_guards([g])
expect msgs.len() == 0
```

</details>

#### a forbidden call fails the example and names the mock and the reason

- a forbidden call fails the example and names the mock and the reason
- declare a prevention mock for the deprecated writer
- code under test takes the forbidden path
- check_guards reports exactly one failure naming mock and reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a forbidden call fails the example and names the mock and the reason")
step("declare a prevention mock for the deprecated writer")
val m = MockFunction.new("legacy_write")
val reason = "legacy_write is deprecated; use write_v2"
step("code under test takes the forbidden path")
m.record_call(["/tmp/x"])
step("check_guards reports exactly one failure naming mock and reason")
val msgs = check_guards([ForbiddenCallGuard.new(m, reason)])
expect msgs.len() == 1
expect msgs[0].contains("legacy_write")
expect msgs[0].contains(reason)
```

</details>

#### prevent_at_most allows the budget and fails on budget+1

- prevent_at_most allows the budget and fails on budget+1
- declare a budget guard: at most 2 retries
- two calls stay within budget
- a third call exceeds the budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("prevent_at_most allows the budget and fails on budget+1")
step("declare a budget guard: at most 2 retries")
val m = MockFunction.new("retry_call")
val reason = "at most 2 retries allowed"
step("two calls stay within budget")
m.record_call([])
m.record_call([])
val within_budget = check_guards([ForbiddenCallGuard.at_most(m, 2, reason)])
expect within_budget.len() == 0
step("a third call exceeds the budget")
m.record_call([])
val over_budget = check_guards([ForbiddenCallGuard.at_most(m, 2, reason)])
expect over_budget.len() == 1
expect over_budget[0].contains("retry_call")
```

</details>

#### verify_called with zero times is the manual equivalent

- verify_called with zero times is the manual equivalent
- the old idiom: was_called_n_times(0) after the fact
- a guard expresses the same intent declaratively


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verify_called with zero times is the manual equivalent")
step("the old idiom: was_called_n_times(0) after the fact")
val m = MockFunction.new("network_send")
expect m.was_called_n_times(0)
m.record_call([])
expect m.was_called_n_times(0) == false
step("a guard expresses the same intent declaratively")
val msgs = check_guards([ForbiddenCallGuard.new(m, "network is banned in unit specs")])
expect msgs.len() == 1
```

</details>

### prevention mock file scope

#### prevent_file guard is checked on every example

- prevent_file guard is checked on every example
- share one mock, simulating file-scope placement at the top of a spec
- example 1: mock untouched stays green
- example 2 (simulated): forbidden call happens
- example 3 (simulated): still recorded, still red until the mock is reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("prevent_file guard is checked on every example")
step("share one mock, simulating file-scope placement at the top of a spec")
val m = MockFunction.new("real_http_send")
val reason = "unit specs must not hit the network"
step("example 1: mock untouched stays green")
expect check_guards([ForbiddenCallGuard.new(m, reason)]).len() == 0
step("example 2 (simulated): forbidden call happens")
m.record_call(["GET", "http://example.com"])
expect check_guards([ForbiddenCallGuard.new(m, reason)]).len() == 1
step("example 3 (simulated): still recorded, still red until the mock is reset")
expect check_guards([ForbiddenCallGuard.new(m, reason)]).len() == 1
```

</details>

#### file guard failure message carries the file-scope reason

- file guard failure message carries the file-scope reason
- share a file-scope mock for a network seam
- code under test hits the network
- the failure message names both the mock and the file-scope reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("file guard failure message carries the file-scope reason")
step("share a file-scope mock for a network seam")
val m = MockFunction.new("real_http_send")
val reason = "unit specs must not hit the network"
step("code under test hits the network")
m.record_call(["POST", "http://example.com"])
step("the failure message names both the mock and the file-scope reason")
val msgs = check_guards([ForbiddenCallGuard.new(m, reason)])
expect msgs.len() == 1
expect msgs[0].contains("real_http_send")
expect msgs[0].contains(reason)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-PREVENT-MOCK-1`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6ec3a8917b6705bf3a88a19a1acf2a566de06c49beebadcc450b13db3d543732`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ec3a8917b6705bf3a88a19a1acf2a566de06c49beebadcc450b13db3d543732`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ec3a8917b6705bf3a88a19a1acf2a566de06c49beebadcc450b13db3d543732`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/std/testing/prevention_mock_spec.spl
mirror: doc/06_spec/01_unit/lib/std/testing/prevention_mock_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/testing/prevention_mock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/testing/prevention_mock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/testing/prevention_mock_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a prevention mock that is never called leaves the example green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/testing/prevention_mock_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a forbidden call fails the example and names the mock and the reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/testing/prevention_mock_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prevent_at_most allows the budget and fails on budget+1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
