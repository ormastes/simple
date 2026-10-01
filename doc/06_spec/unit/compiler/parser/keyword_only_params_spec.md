# Keyword Only Params Specification

> Tests covering keyword-only params (~).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Keyword Only Params Specification

## Scenarios

### keyword-only params (~)

#### function with named params is callable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- function with named params is callable
   - Expected: result equals `Hello, Alice!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function with named params is callable")
val result = greet(name: "Alice", greeting: "Hello")
expect(result).to_equal("Hello, Alice!")
```

</details>

#### mixed positional and named params work

- mixed positional and named params work
   - Expected: result equals `example.com:443`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed positional and named params work")
val result = configure("example.com", 443, false)
expect(result).to_equal("example.com:443")
```

</details>

#### keyword-only param with debug enabled

- keyword-only param with debug enabled
   - Expected: result equals `localhost:8080 [debug]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keyword-only param with debug enabled")
val result = configure("localhost", 8080, true)
expect(result).to_equal("localhost:8080 [debug]")
```

</details>

#### named params in any order

- named params in any order
   - Expected: result equals `Hi, Bob!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("named params in any order")
val result = greet(greeting: "Hi", name: "Bob")
expect(result).to_equal("Hi, Bob!")
```

</details>

#### simple add function with named params

- simple add function with named params
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple add function with named params")
val result = add(a: 3, b: 4)
expect(result).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/keyword_only_params_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering keyword-only params (~).
- keyword-only params (~)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `387509f39787da111df0faa59315e9c43fa94c6440dac56fd1b7af31512cf95c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `387509f39787da111df0faa59315e9c43fa94c6440dac56fd1b7af31512cf95c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `387509f39787da111df0faa59315e9c43fa94c6440dac56fd1b7af31512cf95c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/parser/keyword_only_params_spec.spl
mirror: doc/06_spec/unit/compiler/parser/keyword_only_params_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/keyword_only_params_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/keyword_only_params_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/keyword_only_params_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/keyword_only_params_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function with named params is callable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/keyword_only_params_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mixed positional and named params work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/keyword_only_params_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keyword-only param with debug enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
