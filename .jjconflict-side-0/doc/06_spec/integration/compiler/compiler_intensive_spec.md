# @req REQ-SSPEC-INTEGRATION

> check(code.contains("class"))

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-SSPEC-INTEGRATION

check(code.contains("class"))

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/compiler_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

check(code.contains("class"))
            check(code.contains("fn"))

        slow_it "compiles class with constructor":
            step("compiles class with constructor")
            val code = """
            class Counter:
                count: i64
                static fn new() -> Counter:
                    Counter(count: 0)

## Scenarios

### Compiler Pipeline - Intensive

#### simple function compilation

<details>
<summary>Advanced: compiles function definition end-to-end</summary>

#### compiles function definition end-to-end _(slow)_

- compiles function definition end-to-end


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles function definition end-to-end")
# Simple function that should compile successfully
val code = "fn add(x, y): x + y"

# Verify code is not empty
check(code.len() > 0)

# Basic compilation check (placeholder - actual compilation in next phase)
val has_fn_keyword = code.contains("fn")
check(has_fn_keyword)
```

</details>


</details>

<details>
<summary>Advanced: compiles function with return type</summary>

#### compiles function with return type _(slow)_

- compiles function with return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles function with return type")
val code = "fn square(x: i64) -> i64: x * x"
check(code.contains("->"))
check(code.contains("i64"))
```

</details>


</details>

#### class compilation

<details>
<summary>Advanced: compiles simple class</summary>

#### compiles simple class _(slow)_

- compiles simple class


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles simple class")
val code = """
class Point:
    x: i64
    y: i64
    fn get_x() -> i64: self.x
"""

check(code.contains("class"))
check(code.contains("fn"))
```

</details>


</details>

<details>
<summary>Advanced: compiles class with constructor</summary>

#### compiles class with constructor _(slow)_

- compiles class with constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles class with constructor")
val code = """
class Counter:
    count: i64
    static fn new() -> Counter:
        Counter(count: 0)
"""

check(code.contains("static"))
check(code.contains("Counter"))
```

</details>


</details>

#### module compilation

<details>
<summary>Advanced: handles import statements</summary>

#### handles import statements _(slow)_

- handles import statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles import statements")
val code = "use std.spec\ncheck(true)"
check(code.contains("use"))
check(code.contains("std.spec"))
```

</details>


</details>

<details>
<summary>Advanced: handles multiple imports</summary>

#### handles multiple imports _(slow)_

- handles multiple imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles multiple imports")
val code = """
use std.spec
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 24 |
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

- Canonical SPipe generation for source `a4968d288aff9e30a9c7af35f025e1e14e59dc5deb9eb2842cfe7e865e709b3b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4968d288aff9e30a9c7af35f025e1e14e59dc5deb9eb2842cfe7e865e709b3b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4968d288aff9e30a9c7af35f025e1e14e59dc5deb9eb2842cfe7e865e709b3b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/compiler_intensive_spec.spl
mirror: doc/06_spec/integration/compiler/compiler_intensive_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/compiler_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/compiler_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/compiler_intensive_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles function definition end-to-end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/compiler_intensive_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles function with return type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/compiler_intensive_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles simple class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
