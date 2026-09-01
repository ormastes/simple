# Sfnt Static Axes Font Admission Specification

> Tests covering the two pinned static-axes faces are readable at their catalog sizes, static-axes faces parse as sfnt, the axes manifest is NOT what rejects them, full admission decision — the actual contract the desktop lane needs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sfnt Static Axes Font Admission Specification

## Scenarios

### the two pinned static-axes faces are readable at their catalog sizes

#### Bungee-Regular.ttf is present at 118996 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Bungee-Regular.ttf is present at 118996 bytes
   - Expected: file_read_bytes(BUNGEE).len() equals `118996`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Bungee-Regular.ttf is present at 118996 bytes")
expect(file_read_bytes(BUNGEE).len()).to_equal(118996)
```

</details>

#### UnifrakturCook-Bold.ttf is present at 42688 bytes

- UnifrakturCook-Bold.ttf is present at 42688 bytes
   - Expected: file_read_bytes(UNIFRAKTUR).len() equals `42688`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("UnifrakturCook-Bold.ttf is present at 42688 bytes")
expect(file_read_bytes(UNIFRAKTUR).len()).to_equal(42688)
```

</details>

### static-axes faces parse as sfnt

#### Bungee has a parseable offset table

- Bungee has a parseable offset table
   - Expected: parse_offset_table(file_read_bytes(BUNGEE)) == None is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Bungee has a parseable offset table")
expect(parse_offset_table(file_read_bytes(BUNGEE)) == None).to_equal(false)
```

</details>

#### UnifrakturCook has a parseable offset table

- UnifrakturCook has a parseable offset table
   - Expected: parse_offset_table(file_read_bytes(UNIFRAKTUR)) == None is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("UnifrakturCook has a parseable offset table")
expect(parse_offset_table(file_read_bytes(UNIFRAKTUR)) == None).to_equal(false)
```

</details>

### the axes manifest is NOT what rejects them

#### Bungee matches the \

- Bungee matches the \
   - Expected: sfnt_manifest_default_axes_match(file_read_bytes(BUNGEE), "static") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Bungee matches the \")
expect(sfnt_manifest_default_axes_match(file_read_bytes(BUNGEE), "static")).to_equal(true)
```

</details>

#### UnifrakturCook matches the \

- UnifrakturCook matches the \
   - Expected: sfnt_manifest_default_axes_match(file_read_bytes(UNIFRAKTUR), "static") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("UnifrakturCook matches the \")
expect(sfnt_manifest_default_axes_match(file_read_bytes(UNIFRAKTUR), "static")).to_equal(true)
```

</details>

### full admission decision — the actual contract the desktop lane needs

#### Bungee passes default-glyf format validation

- Bungee passes default-glyf format validation
   - Expected: validate_default_glyf_font(file_read_bytes(BUNGEE)).supported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Bungee passes default-glyf format validation")
expect(validate_default_glyf_font(file_read_bytes(BUNGEE)).supported).to_equal(true)
```

</details>

#### UnifrakturCook passes default-glyf format validation

- UnifrakturCook passes default-glyf format validation
   - Expected: validate_default_glyf_font(file_read_bytes(UNIFRAKTUR)).supported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("UnifrakturCook passes default-glyf format validation")
expect(validate_default_glyf_font(file_read_bytes(UNIFRAKTUR)).supported).to_equal(true)
```

</details>

#### Bungee is admitted as a static instance

- Bungee is admitted as a static instance
   - Expected: validate_glyf_font_instance(file_read_bytes(BUNGEE), "static").supported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Bungee is admitted as a static instance")
expect(validate_glyf_font_instance(file_read_bytes(BUNGEE), "static").supported).to_equal(true)
```

</details>

#### UnifrakturCook is admitted as a static instance

- UnifrakturCook is admitted as a static instance
   - Expected: validate_glyf_font_instance(file_read_bytes(UNIFRAKTUR), "static").supported is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("UnifrakturCook is admitted as a static instance")
expect(validate_glyf_font_instance(file_read_bytes(UNIFRAKTUR), "static").supported).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering the two pinned static-axes faces are readable at their catalog sizes, static-axes faces parse as sfnt, the axes manifest is NOT what rejects them, full admission decision — the actual contract the desktop lane needs.
- the two pinned static-axes faces are readable at their catalog sizes
- static-axes faces parse as sfnt
- the axes manifest is NOT what rejects them
- full admission decision — the actual contract the desktop lane needs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9811b4886d649ffba4335744b6adf3b74911c6d91bf007ba8b8465c718e65500`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9811b4886d649ffba4335744b6adf3b74911c6d91bf007ba8b8465c718e65500`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9811b4886d649ffba4335744b6adf3b74911c6d91bf007ba8b8465c718e65500`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Bungee-Regular.ttf is present at 118996 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UnifrakturCook-Bold.ttf is present at 42688 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/sfnt_static_axes_font_admission_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Bungee has a parseable offset table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
