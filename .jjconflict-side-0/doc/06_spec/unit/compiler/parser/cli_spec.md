# Cli Specification

> Tests covering TreeSitter CLI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Specification

## Scenarios

### TreeSitter CLI

#### language detection

#### detects simple, python, rust, and unknown sources

- run LanguageDetector.detect over four source samples
   - Expected: det.detect("fn main():\n    0\n").language equals `simple`
   - Expected: det.detect("def f():\n    pass\n").language equals `python`
   - Expected: det.detect("let x = 1;\n").language equals `rust`
   - Expected: det.detect("+++???\n").language equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("run LanguageDetector.detect over four source samples")
val det = LanguageDetector.new()
expect(det.detect("fn main():\n    0\n").language).to_equal("simple")
expect(det.detect("def f():\n    pass\n").language).to_equal("python")
expect(det.detect("let x = 1;\n").language).to_equal("rust")
expect(det.detect("+++???\n").language).to_equal("unknown")
```

</details>

#### grammar parsing

#### parses a grammar-like source into an outline

- run treesitter_new + parse_outline_heuristic on a fixture
   - Expected: mod.functions.len() equals `2`
   - Expected: mod.functions[0].name equals `alpha`
   - Expected: mod.functions[1].name equals `beta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("run treesitter_new + parse_outline_heuristic on a fixture")
val src = "fn alpha(a: i64) -> i64:\n    a\n\nfn beta():\n    0\n"
val mod: OutlineModule = treesitter_new(src).parse_outline_heuristic()
expect(mod.functions.len()).to_equal(2)
expect(mod.functions[0].name).to_equal("alpha")
expect(mod.functions[1].name).to_equal("beta")
```

</details>

#### stays error-tolerant on malformed input

- parse a syntactically broken fixture, assert no crash
   - Expected: mod.functions[0].name equals `broken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parse a syntactically broken fixture, assert no crash")
val broken = "fn broken( <<< !!\n"
val mod: OutlineModule = treesitter_new(broken).parse_outline_heuristic()
expect(mod.functions[0].name).to_equal("broken")
```

</details>

#### grammar validation

#### distinguishes detected languages from unknown by confidence

- check DetectionResult confidence for known vs unknown
   - Expected: det.detect("+++").confidence equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("check DetectionResult confidence for known vs unknown")
val det = LanguageDetector.new()
expect(det.detect("fn x():\n    0\n").confidence).to_be_greater_than(0.5)
expect(det.detect("+++").confidence).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/cli_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TreeSitter CLI.
- TreeSitter CLI

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36397f497f6a0317899c62d0666e352cb499544a45e132ea428476d2825d1504`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36397f497f6a0317899c62d0666e352cb499544a45e132ea428476d2825d1504`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36397f497f6a0317899c62d0666e352cb499544a45e132ea428476d2825d1504`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/unit/compiler/parser/cli_spec.spl
mirror: doc/06_spec/unit/compiler/parser/cli_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/cli_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/compiler/parser/cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/parser/cli_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects simple, python, rust, and unknown sources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/cli_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a grammar-like source into an outline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/cli_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays error-tolerant on malformed input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
