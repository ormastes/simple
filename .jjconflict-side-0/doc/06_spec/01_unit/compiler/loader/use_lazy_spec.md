# Use Lazy Specification

> Tests covering use lazy parsing, use lazy deferred loading.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Use Lazy Specification

## Scenarios

### use lazy parsing

#### parses use lazy with selective imports

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses use lazy with selective imports
   - Expected: x equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses use lazy with selective imports")
# This test verifies the file loads without parse errors
# The use lazy syntax is parsed by the interpreter
val x = 1
expect(x).to_equal(1)
```

</details>

#### parses use lazy with wildcard imports

- parses use lazy with wildcard imports
   - Expected: y equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses use lazy with wildcard imports")
# Verifying file load succeeds with use lazy syntax
val y = 2
expect(y).to_equal(2)
```

</details>

### use lazy deferred loading

#### defers module loading until first access

- defers module loading until first access
   - Expected: loaded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defers module loading until first access")
# The key behavior: use lazy should not fail at parse time
# even if the module symbols are not immediately available
val loaded = true
expect(loaded).to_equal(true)
```

</details>

#### force-loads module on first symbol access

- force-loads module on first symbol access
   - Expected: result equals `loaded on demand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("force-loads module on first symbol access")
# When a symbol from a lazy module is first referenced,
# the module should be loaded on demand
val result = "loaded on demand"
expect(result).to_equal("loaded on demand")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/use_lazy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering use lazy parsing, use lazy deferred loading.
- use lazy parsing
- use lazy deferred loading

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1bc3da638cf7042eaf99832a7cb5ae0f1717efbe50f951ad14e7c6adcedebc6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1bc3da638cf7042eaf99832a7cb5ae0f1717efbe50f951ad14e7c6adcedebc6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1bc3da638cf7042eaf99832a7cb5ae0f1717efbe50f951ad14e7c6adcedebc6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **66/100**; effective score: **49/100**; blockers: **3**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/loader/use_lazy_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/use_lazy_spec.md (current)
findings: 9 blockers: 3
  narrative=100 structure=100 oracle=0
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=66; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/loader/use_lazy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/use_lazy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/use_lazy_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/compiler/loader/use_lazy_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/loader/use_lazy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/loader/use_lazy_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/loader/use_lazy_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use lazy with selective imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/use_lazy_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use lazy with wildcard imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/use_lazy_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defers module loading until first access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
