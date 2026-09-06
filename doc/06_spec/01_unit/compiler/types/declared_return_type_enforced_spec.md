# Declared Return Type Enforced Specification

> Tests covering declared function return types are enforced.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Declared Return Type Enforced Specification

## Scenarios

### declared function return types are enforced

#### rejects a text literal returned from a -> bool signature

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a text literal returned from a -> bool signature
- Compile and run the violating fixture under the strictest assurance profile
- A -> bool function returning text is a type error and must be reported as one
- The wrong value must NOT be handed to the caller as if it were a bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a text literal returned from a -> bool signature")
step("Compile and run the violating fixture under the strictest assurance profile")
val out = run_fixture(BAD, "interpreter", "critical")

step("A -> bool function returning text is a type error and must be reported as one")
expect(out).to_contain("[typecheck]")

step("The wrong value must NOT be handed to the caller as if it were a bool")
assert_false(out.contains("ret_text => not-a-bool"))
```

</details>

#### still accepts a matching return type under the same strict profile

- still accepts a matching return type under the same strict profile
- Run the control fixture, whose return value matches its declaration
- The control proves enforcement is discriminating rather than rejecting everything


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still accepts a matching return type under the same strict profile")
step("Run the control fixture, whose return value matches its declaration")
val out = run_fixture(OK, "interpreter", "critical")

step("The control proves enforcement is discriminating rather than rejecting everything")
expect(out).to_contain("ret_bool => true")
assert_false(out.contains("[typecheck]"))
```

</details>

#### does not let the two engines disagree about the same function

- does not let the two engines disagree about the same function
- Run the violating fixture on both engines with enforcement off, as a user would today
- An unenforced return type lets each backend invent its own answer: the JIT prints a raw slot (<special:NNN>, a tagged heap pointer), the interpreter passes the text straight through
- Whatever the engines do, they must not silently produce two different values for one function


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not let the two engines disagree about the same function")
step("Run the violating fixture on both engines with enforcement off, as a user would today")
val jit = run_fixture(BAD, "jit", "")
val interp = run_fixture(BAD, "interpreter", "")

step("An unenforced return type lets each backend invent its own answer: the JIT prints a raw slot (<special:NNN>, a tagged heap pointer), the interpreter passes the text straight through")
step("Whatever the engines do, they must not silently produce two different values for one function")
assert_false(jit.contains("<special:") and interp.contains("not-a-bool"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/types/declared_return_type_enforced_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering declared function return types are enforced.
- declared function return types are enforced

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `1a1edce8e0f42ccb1ed3f2fbd4ebdec34f7773f0d24bc3b00a5943d7902c024c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a1edce8e0f42ccb1ed3f2fbd4ebdec34f7773f0d24bc3b00a5943d7902c024c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a1edce8e0f42ccb1ed3f2fbd4ebdec34f7773f0d24bc3b00a5943d7902c024c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/types/declared_return_type_enforced_spec.spl
mirror: doc/06_spec/01_unit/compiler/types/declared_return_type_enforced_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/types/declared_return_type_enforced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/types/declared_return_type_enforced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/types/declared_return_type_enforced_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a text literal returned from a -> bool signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/declared_return_type_enforced_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still accepts a matching return type under the same strict profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/declared_return_type_enforced_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not let the two engines disagree about the same function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
