# Formatter Specification

> Tests covering formatter lexical safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Specification

## Scenarios

### formatter lexical safety

#### formats ordinary code idempotently

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats ordinary code idempotently


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats ordinary code idempotently")
val formatter = make_formatter()
match formatter.format_source("val x=1+2"):
    case Err(error):
        fail("unexpected formatter rejection: {error}")
    case Ok(formatted):
        expect(formatted).to_contain("val x = 1 + 2")
        match formatter.format_source(formatted):
            case Err(error): fail("formatter lost idempotence: {error}")
            case Ok(twice): expect(twice).to_equal(formatted)
```

</details>

#### accepts an existing empty file

- accepts an existing empty file
   - Expected: file_write(path, "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts an existing empty file")
val path = "/tmp/simple_formatter_empty_file.spl"
expect(file_write(path, "")).to_equal(true)
match make_formatter().format_file(path):
    case Err(error): fail("empty file rejected: {error}")
    case Ok(formatted): expect(formatted).to_equal("")
val _ = file_delete(path)
```

</details>

#### preserves parser-required generic cast adjacency

- preserves parser-required generic cast adjacency
   - Expected: formatted does not contain `BoundedChannel <`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves parser-required generic cast adjacency")
val formatter = make_formatter()
match formatter.format_source("val ch = event_channel as BoundedChannel<UIEvent>"):
    case Err(error): fail("generic cast rejected: {error}")
    case Ok(formatted):
        expect(formatted).to_contain("BoundedChannel<UIEvent>")
        expect(formatted.contains("BoundedChannel <")).to_equal(false)
        match formatter.format_source(formatted):
            case Err(error): fail("generic cast lost idempotence: {error}")
            case Ok(twice): expect(twice).to_equal(formatted)
```

</details>

#### preserves branch indentation after returns

- preserves branch indentation after returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves branch indentation after returns")
val formatter = make_formatter()
val source = "fn classify(value: i64) -> i64:\n    if value < 0:\n        return -1\n    elif value == 0:\n        return 0\n    else:\n        return 1"
match formatter.format_source(source):
    case Err(error): fail("branch indentation rejected: {error}")
    case Ok(formatted):
        expect(formatted).to_contain("\n    elif value == 0:")
        expect(formatted).to_contain("\n    else:")
        match formatter.format_source(formatted):
            case Err(error): fail("branch indentation lost idempotence: {error}")
            case Ok(twice): expect(twice).to_equal(formatted)
```

</details>

#### preserves literals comments and raw payloads or rejects the rewrite

- preserves literals comments and raw payloads or rejects the rewrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves literals comments and raw payloads or rejects the rewrite")
expect_formatter_preserves_or_rejects(
    "val url = \"https://api.example.test/a+b?q=x,y\"",
    "\"https://api.example.test/a+b?q=x,y\""
)
expect_formatter_preserves_or_rejects(
    "val x = 1  # keep  a+b, https://a/b",
    "# keep  a+b, https://a/b"
)
expect_formatter_preserves_or_rejects(
    "val raw = r\"C:\\\\tmp\\\\{literal}+a,b\"",
    "r\"C:\\\\tmp\\\\{literal}+a,b\""
)
expect_formatter_preserves_or_rejects(
    "val doc = \"\"\"first  + line\n    second / line\n\nthird\"\"\"",
    "\"\"\"first  + line\n    second / line\n\nthird\"\"\""
)
expect_formatter_preserves_or_rejects(
    "val output = sh{\necho a  b | sed 's/a/b/'\n}",
    "echo a  b | sed 's/a/b/'"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering formatter lexical safety.
- formatter lexical safety

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

- Canonical SPipe generation for source `551e3c135887b3278853f1dbdc2c3c628e5ade1a2e7deeb1319ad329fd5cc839`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `551e3c135887b3278853f1dbdc2c3c628e5ade1a2e7deeb1319ad329fd5cc839`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `551e3c135887b3278853f1dbdc2c3c628e5ade1a2e7deeb1319ad329fd5cc839`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/formatter_spec.spl
mirror: doc/06_spec/01_unit/app/formatter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/formatter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/formatter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/formatter_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats ordinary code idempotently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/formatter_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an existing empty file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/formatter_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves parser-required generic cast adjacency' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
