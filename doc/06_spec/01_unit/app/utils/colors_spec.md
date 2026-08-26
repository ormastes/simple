# Colors Specification

> Tests covering colors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Colors Specification

## Scenarios

### colors

#### generates escape character

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates escape character
   - Expected: colors.esc_char().len() equals `1`
   - Expected: colors.esc_char() equals `{char_from_code(27)}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates escape character")
expect(colors.esc_char().len()).to_equal(1)
expect(colors.esc_char()).to_equal("{char_from_code(27)}")
```

</details>

#### generates reset code

- generates reset code
   - Expected: colors.reset().len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates reset code")
expect(colors.reset()).to_contain("[0m")
expect(colors.reset().len()).to_equal(4)
```

</details>

#### generates foreground colors

- generates foreground colors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates foreground colors")
expect(colors.red()).to_contain("[31m")
expect(colors.green()).to_contain("[32m")
expect(colors.yellow()).to_contain("[33m")
expect(colors.blue()).to_contain("[34m")
expect(colors.magenta()).to_contain("[35m")
expect(colors.cyan()).to_contain("[36m")
expect(colors.white()).to_contain("[37m")
```

</details>

#### generates background colors

- generates background colors


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("generates background colors")
expect(colors.bg_black()).to_contain("[40m")
expect(colors.bg_red()).to_contain("[41m")
expect(colors.bg_green()).to_contain("[42m")
expect(colors.bg_blue()).to_contain("[44m")
expect(colors.bg_white()).to_contain("[47m")
```

</details>

#### wraps text with semantic colors

- wraps text with semantic colors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("wraps text with semantic colors")
val s = colors.success("ok")
expect(s).to_start_with(colors.green())
expect(s).to_end_with(colors.reset())
expect(s).to_contain("ok")
expect(colors.error("bad")).to_start_with(colors.red())
expect(colors.warning("warn")).to_start_with(colors.yellow())
expect(colors.info("note")).to_start_with(colors.cyan())
```

</details>

#### strips color codes from text

- strips color codes from text
   - Expected: colored contains `mixed`
   - Expected: colors.strip_colors(colored) equals `mixed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("strips color codes from text")
val colored = colors.success(colors.error("mixed"))
expect(colored.contains("mixed")).to_equal(true)
expect(colors.strip_colors(colored)).to_equal("mixed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/utils/colors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering colors.
- colors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e77bc30d4645baf604d374661a6c458cc829448b251cf21e3ce4c1809877b68d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e77bc30d4645baf604d374661a6c458cc829448b251cf21e3ce4c1809877b68d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e77bc30d4645baf604d374661a6c458cc829448b251cf21e3ce4c1809877b68d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/utils/colors_spec.spl
mirror: doc/06_spec/01_unit/app/utils/colors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/utils/colors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/utils/colors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/utils/colors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/utils/colors_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates escape character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/utils/colors_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates reset code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/utils/colors_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates foreground colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
