# T32 Cli Render Specification

> Tests covering T32 CLI Render.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Render Specification

## Scenarios

### T32 CLI Render

#### scalar results

#### renders scalar value

- renders scalar value
   - Expected: output equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders scalar value")
val result = make_scalar("42")
val output = render_result(result)
expect(output).to_equal("42")
```

</details>

#### renders scalar with title

- renders scalar with title
   - Expected: output equals `Register PC: 0x08001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders scalar with title")
val result = make_scalar_titled("Register PC", "0x08001000")
val output = render_result(result)
expect(output).to_equal("Register PC: 0x08001000")
```

</details>

#### table results

#### renders table with header and separator

- renders table with header and separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders table with header and separator")
val rows: [[text]] = [["Name", "Value"], ["PC", "0x1000"], ["SP", "0x2000"]]
val result = make_table("Registers", rows)
val output = render_result(result)
expect(output).to_contain("Registers:")
expect(output).to_contain("Name")
expect(output).to_contain("Value")
expect(output).to_contain("PC")
expect(output).to_contain("SP")
# Header separator line of dashes should be present
expect(output).to_contain("----")
```

</details>

#### renders empty table as (empty)

- renders empty table as (empty)
   - Expected: output equals `Empty: (empty)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders empty table as (empty)")
val result = make_table("Empty", [])
val output = render_result(result)
expect(output).to_equal("Empty: (empty)")
```

</details>

#### kv results

#### renders aligned key-value pairs

- renders aligned key-value pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders aligned key-value pairs")
val pairs: [[text]] = [["host", "localhost"], ["port", "20000"]]
val result = make_kv("Session", pairs)
val output = render_result(result)
expect(output).to_start_with("Session:")
expect(output).to_contain("host")
expect(output).to_contain("localhost")
expect(output).to_contain("port")
expect(output).to_contain("20000")
```

</details>

#### list results

#### renders bulleted items

- renders bulleted items


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders bulleted items")
val items: [text] = ["alpha", "beta", "gamma"]
val result = make_list("Items", items)
val output = render_result(result)
expect(output).to_start_with("Items:")
expect(output).to_contain("  - alpha")
expect(output).to_contain("  - beta")
expect(output).to_contain("  - gamma")
```

</details>

#### raw output

#### passes through raw text

- passes through raw text
   - Expected: output equals `some raw output\nline two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through raw text")
val result = make_raw("some raw output\nline two")
val output = render_result(result)
expect(output).to_equal("some raw output\nline two")
```

</details>

#### error formatting

#### formats error message

- formats error message
   - Expected: output equals `Error: Connection lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats error message")
val output = render_error("Connection lost")
expect(output).to_equal("Error: Connection lost")
```

</details>

#### formats empty error

- formats empty error
   - Expected: output equals `Error: `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats empty error")
val output = render_error("")
expect(output).to_equal("Error: ")
```

</details>

#### gui_status footer

#### appends gui status footer to scalar

- appends gui status footer to scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends gui status footer to scalar")
var result = make_scalar("ok")
result.gui_status = "{\"cpu_state\":\"stopped\",\"practice_state\":\"idle\"}"
val output = render_result(result)
expect(output).to_contain("ok")
expect(output).to_contain("[CPU: stopped | PRACTICE: idle]")
```

</details>

#### skips empty gui status

- skips empty gui status
   - Expected: output equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips empty gui status")
var result = make_scalar("ok")
result.gui_status = ""
val output = render_result(result)
expect(output).to_equal("ok")
```

</details>

#### skips empty object gui status

- skips empty object gui status
   - Expected: output equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips empty object gui status")
var result = make_scalar("ok")
result.gui_status = "{}"
val output = render_result(result)
expect(output).to_equal("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/t32_cli/t32_cli_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 CLI Render.
- T32 CLI Render

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `5f3a2316582cca38ee4be6551e4b0a99d14bf9c6ae42077687754ed58449ace1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f3a2316582cca38ee4be6551e4b0a99d14bf9c6ae42077687754ed58449ace1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f3a2316582cca38ee4be6551e4b0a99d14bf9c6ae42077687754ed58449ace1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/t32_cli/t32_cli_render_spec.spl
mirror: doc/06_spec/unit/app/t32_cli/t32_cli_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/t32_cli/t32_cli_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/t32_cli/t32_cli_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/t32_cli/t32_cli_render_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders scalar value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/t32_cli_render_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders scalar with title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/t32_cli_render_spec.spl:233:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders table with header and separator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
