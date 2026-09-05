# Label Token Specification

> Tests covering label tokens for labeled break/continue.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Label Token Specification

## Scenarios

### label tokens for labeled break/continue

<details>
<summary>Advanced: labeled break exits outer loop (via fn return)</summary>

#### labeled break exits outer loop (via fn return)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- labeled break exits outer loop (via fn return)
   - Expected: found equals `22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("labeled break exits outer loop (via fn return)")
val found = search_2d(2, 2)
expect(found).to_equal(22)
```

</details>


</details>

#### labeled continue effect (count outer iters not triggering inner)

- labeled continue effect (count outer iters not triggering inner)
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("labeled continue effect (count outer iters not triggering inner)")
# When inner loop always triggers 'continue outer' at j==1,
# the outer iteration count remains 0
val count = count_outer_iters()
expect(count).to_equal(0)
```

</details>

<details>
<summary>Advanced: unlabeled break only exits inner loop</summary>

#### unlabeled break only exits inner loop

- unlabeled break only exits inner loop
   - Expected: total equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unlabeled break only exits inner loop")
var total = 0
for i in 0..3:
    for j in 0..10:
        if j == 2:
            break
    total = total + 1
expect(total).to_equal(3)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/label_token_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering label tokens for labeled break/continue.
- label tokens for labeled break/continue

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

- Canonical SPipe generation for source `be7bf507f932bbf0e874f3e0cc3e2c99768020cabc8c2194b0075a31cdf933a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be7bf507f932bbf0e874f3e0cc3e2c99768020cabc8c2194b0075a31cdf933a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be7bf507f932bbf0e874f3e0cc3e2c99768020cabc8c2194b0075a31cdf933a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lexer/label_token_spec.spl
mirror: doc/06_spec/01_unit/compiler/lexer/label_token_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lexer/label_token_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lexer/label_token_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lexer/label_token_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lexer/label_token_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'labeled break exits outer loop (via fn return)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/label_token_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'labeled continue effect (count outer iters not triggering inner)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/label_token_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unlabeled break only exits inner loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
