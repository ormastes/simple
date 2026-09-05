# Import Parser Specification

> Tests covering Import Parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import Parser Specification

## Scenarios

### Import Parser

#### parses source with no imports

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses source with no imports
   - Expected: result.imports.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses source with no imports")
val source = "fn main(): 0\n"
val result = parse_source("test.spl", source)
expect(result.imports.len()).to_equal(0)
```

</details>

#### parses source with one import

- parses source with one import
   - Expected: result.imports.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses source with one import")
val source = "import foo.bar\nfn main(): 0\n"
val result = parse_source("test.spl", source)
expect(result.imports.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/depgraph/import_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Import Parser.
- Import Parser

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7785186fcc6ae2eaa1aea9c3988c89537ac0bc388ec91d81b079afd4ca6b283a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7785186fcc6ae2eaa1aea9c3988c89537ac0bc388ec91d81b079afd4ca6b283a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7785186fcc6ae2eaa1aea9c3988c89537ac0bc388ec91d81b079afd4ca6b283a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/depgraph/import_parser_spec.spl
mirror: doc/06_spec/unit/app/depgraph/import_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/depgraph/import_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/depgraph/import_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/depgraph/import_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/depgraph/import_parser_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses source with no imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/depgraph/import_parser_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses source with one import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
