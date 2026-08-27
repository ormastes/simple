# Init Parser Specification

> Tests covering InitParser - Comment-based API Documentation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Init Parser Specification

## Scenarios

### InitParser - Comment-based API Documentation

#### parses real __init__.spl file from src/std/spec

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses real __init__.spl file from src/std/spec
   - Expected: has_data is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses real __init__.spl file from src/std/spec")
val spec_init = cwd() + "/src/std/spec/__init__.spl"

if file_exists(spec_init):
    val result = parse_init_file(spec_init)
    val groups = result.0
    val items = result.1

    # Should find at least one group or item
    val has_data = groups.len() > 0 or items.len() > 0
    expect(has_data).to_equal(true)
```

</details>

#### detects group headers correctly

- detects group headers correctly
   - Expected: has_cap1 is true
   - Expected: has_cap2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects group headers correctly")
# Test the pattern matching for group headers
val header1 = "# File operations"
val header2 = "# - file_read"

val has_cap1 = _contains_capital_in_text(header1)
val has_cap2 = header2.contains(" - ")

expect(has_cap1).to_equal(true)
expect(has_cap2).to_equal(true)
```

</details>

#### extracts item names from dash lines

- extracts item names from dash lines
   - Expected: has_dash1 is true
   - Expected: has_dash2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts item names from dash lines")
# These patterns should be recognized as items
val line1 = "#   - file_read"
val line2 = "# - dir_create()"

val has_dash1 = line1.contains(" - ")
val has_dash2 = line2.contains(" - ")

expect(has_dash1).to_equal(true)
expect(has_dash2).to_equal(true)
```

</details>

#### detects use statements for function extraction

- detects use statements for function extraction
   - Expected: is_use is true
   - Expected: has_braces is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects use statements for function extraction")
val use_line = "use std.spec.{describe, it, expect}"
val is_use = use_line.starts_with("use ")
val has_braces = use_line.contains("{") and use_line.contains("}")

expect(is_use).to_equal(true)
expect(has_braces).to_equal(true)
```

</details>

#### returns empty results for non-existent files

- returns empty results for non-existent files
   - Expected: groups.len() equals `0`
   - Expected: items.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty results for non-existent files")
val fake_path = "/tmp/nonexistent_file.spl"
val result = parse_init_file(fake_path)
val groups = result.0
val items = result.1

expect(groups.len()).to_equal(0)
expect(items.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/doc_coverage/init_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering InitParser - Comment-based API Documentation.
- InitParser - Comment-based API Documentation

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

- Canonical SPipe generation for source `f9d0f61583ee79aa37e233db179d024dd2f4ad8c930ac0eefd0ae4d37b4e0137`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f9d0f61583ee79aa37e233db179d024dd2f4ad8c930ac0eefd0ae4d37b4e0137`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f9d0f61583ee79aa37e233db179d024dd2f4ad8c930ac0eefd0ae4d37b4e0137`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/doc_coverage/init_parser_spec.spl
mirror: doc/06_spec/unit/app/doc_coverage/init_parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/doc_coverage/init_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/doc_coverage/init_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/doc_coverage/init_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/doc_coverage/init_parser_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses real __init__.spl file from src/std/spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/init_parser_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects group headers correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/doc_coverage/init_parser_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts item names from dash lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
