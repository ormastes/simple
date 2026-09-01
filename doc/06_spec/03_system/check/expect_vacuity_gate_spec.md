# expect() vacuity gate

> `expect(<subject>)` with no `to_*` matcher only ever asserted *truthiness*. For a bool subject that is a real assertion, but for any other subject (text, number, list, object) truthiness is trivially true — so the example asserted NOTHING and stayed green forever. Worse, a tail method that is not a matcher but *does* exist on the subject's own type (`expect(s).len()`, `expect(v).contains(x)`) reads exactly like a matcher at a glance while asserting nothing at all.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expect() vacuity gate

`expect(<subject>)` with no `to_*` matcher only ever asserted *truthiness*. For a bool subject that is a real assertion, but for any other subject (text, number, list, object) truthiness is trivially true — so the example asserted NOTHING and stayed green forever. Worse, a tail method that is not a matcher but *does* exist on the subject's own type (`expect(s).len()`, `expect(v).contains(x)`) reads exactly like a matcher at a glance while asserting nothing at all.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/expect_vacuity_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`expect(<subject>)` with no `to_*` matcher only ever asserted *truthiness*. For
a bool subject that is a real assertion, but for any other subject (text,
number, list, object) truthiness is trivially true — so the example asserted
NOTHING and stayed green forever. Worse, a tail method that is not a matcher
but *does* exist on the subject's own type (`expect(s).len()`,
`expect(v).contains(x)`) reads exactly like a matcher at a glance while
asserting nothing at all.

The DSL now counts non-bool `expect(...)` subjects against `to_*` matchers that
actually ran, and fails the example when a subject was never consumed.

## Acceptance

- A non-matcher tail on a non-bool subject FAILS with a `vacuous expect` message.
- A bare `expect(<non-bool>)` FAILS the same way.
- Every correct usage still passes: chained matchers, negated matchers, matchers
  on falsy non-bool subjects, and bare `expect(<bool>)` truthiness.

## Binary note

The negative half runs a fixture through a child compiler. It uses
`$SIMPLE_SPEC_BIN` when set, else `bin/simple`. `bin/simple` is currently a
stale deployed seed that predates this gate; until it is redeployed, verify with
`SIMPLE_SPEC_BIN=src/compiler_rust/target/bootstrap/simple`.

## Scenarios

### expect vacuity gate

#### fails a non-matcher tail on a non-bool subject

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails a non-matcher tail on a non-bool subject
- Run a fixture whose only assertion is expect(text).len()
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails a non-matcher tail on a non-bool subject")
step("Run a fixture whose only assertion is expect(text).len()")
val root = "build/expect-vacuity-gate"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'describe \"f\":\\n    it \"tail\":\\n        expect(\"hello\").len()\\n' > " + root + "/tail_spec.spl && " +
    "${SIMPLE_SPEC_BIN:-bin/simple} test " + root + "/tail_spec.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(output).to_contain("vacuous expect")
expect(output).to_contain("1 total, 0 passed, 1 failed")
expect(code).to_equal(1)
```

</details>

#### fails a bare expect of a non-bool subject

- fails a bare expect of a non-bool subject
- Run a fixture whose only assertion is a bare expect(text)
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails a bare expect of a non-bool subject")
step("Run a fixture whose only assertion is a bare expect(text)")
val root = "build/expect-vacuity-gate-bare"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'describe \"f\":\\n    it \"bare\":\\n        expect(\"hello\")\\n' > " + root + "/bare_spec.spl && " +
    "${SIMPLE_SPEC_BIN:-bin/simple} test " + root + "/bare_spec.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(output).to_contain("vacuous expect")
expect(code).to_equal(1)
```

</details>

#### still passes every correct matcher usage

- still passes every correct matcher usage
- Exercise the matcher forms the gate must not disturb
   - Expected: "hello" equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("still passes every correct matcher usage")
step("Exercise the matcher forms the gate must not disturb")
expect("hello").to_equal("hello")
expect("hello").to_contain("ell")
expect("hello").to_start_with("he")
expect([1, 2, 3]).to_contain(2)
expect(7).to_be_greater_than(3)
```

</details>

#### still passes matchers on falsy non-bool subjects

- still passes matchers on falsy non-bool subjects
- A falsy subject is legitimate when a matcher consumes it
   - Expected: 0 equals `0`
   - Expected: "" equals ``
   - Expected: [] equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("still passes matchers on falsy non-bool subjects")
step("A falsy subject is legitimate when a matcher consumes it")
expect(0).to_equal(0)
expect("").to_equal("")
expect([]).to_equal([])
```

</details>

#### still passes bare truthiness on a bool subject

- still passes bare truthiness on a bool subject
- expect(<bool>) with no matcher remains a real assertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("still passes bare truthiness on a bool subject")
step("expect(<bool>) with no matcher remains a real assertion")
val flag = true
expect(flag)
expect(1 == 1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e8bf388266b8f91c54fd9ab1941c940adbb2e81735af6e49dba505eae31cb12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e8bf388266b8f91c54fd9ab1941c940adbb2e81735af6e49dba505eae31cb12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e8bf388266b8f91c54fd9ab1941c940adbb2e81735af6e49dba505eae31cb12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/expect_vacuity_gate_spec.spl
mirror: doc/06_spec/03_system/check/expect_vacuity_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/expect_vacuity_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/expect_vacuity_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/expect_vacuity_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/expect_vacuity_gate_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails a non-matcher tail on a non-bool subject' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/expect_vacuity_gate_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails a bare expect of a non-bool subject' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/expect_vacuity_gate_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still passes every correct matcher usage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
