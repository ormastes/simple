# CompilerProfile Enum Specification

> Tests for CompilerProfile enum — round-trip text conversion and alias handling. These are pure logic tests that work in interpreter mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CompilerProfile Enum Specification

Tests for CompilerProfile enum — round-trip text conversion and alias handling. These are pure logic tests that work in interpreter mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/01_unit/compiler/config/compiler_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for CompilerProfile enum — round-trip text conversion and alias handling.
These are pure logic tests that work in interpreter mode.

## Scenarios

### CompilerProfile

#### to_text

#### converts Dev to text

- converts Dev to text
   - Expected: profile.to_text() equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Dev to text")
val profile = CompilerProfile.Dev
expect(profile.to_text()).to_equal("dev")
```

</details>

#### converts Test to text

- converts Test to text
   - Expected: profile.to_text() equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Test to text")
val profile = CompilerProfile.Test
expect(profile.to_text()).to_equal("test")
```

</details>

#### converts Prod to text

- converts Prod to text
   - Expected: profile.to_text() equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Prod to text")
val profile = CompilerProfile.Prod
expect(profile.to_text()).to_equal("prod")
```

</details>

#### converts Sdn to text

- converts Sdn to text
   - Expected: profile.to_text() equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Sdn to text")
val profile = CompilerProfile.Sdn
expect(profile.to_text()).to_equal("sdn")
```

</details>

#### from_text

#### parses dev

- parses dev
   - Expected: profile.to_text() equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses dev")
val profile = CompilerProfile.from_text("dev")
expect(profile.to_text()).to_equal("dev")
```

</details>

#### parses development alias

- parses development alias
   - Expected: profile.to_text() equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses development alias")
val profile = CompilerProfile.from_text("development")
expect(profile.to_text()).to_equal("dev")
```

</details>

#### parses test

- parses test
   - Expected: profile.to_text() equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses test")
val profile = CompilerProfile.from_text("test")
expect(profile.to_text()).to_equal("test")
```

</details>

#### parses testing alias

- parses testing alias
   - Expected: profile.to_text() equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses testing alias")
val profile = CompilerProfile.from_text("testing")
expect(profile.to_text()).to_equal("test")
```

</details>

#### parses prod

- parses prod
   - Expected: profile.to_text() equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses prod")
val profile = CompilerProfile.from_text("prod")
expect(profile.to_text()).to_equal("prod")
```

</details>

#### parses production alias

- parses production alias
   - Expected: profile.to_text() equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses production alias")
val profile = CompilerProfile.from_text("production")
expect(profile.to_text()).to_equal("prod")
```

</details>

#### parses release alias

- parses release alias
   - Expected: profile.to_text() equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses release alias")
val profile = CompilerProfile.from_text("release")
expect(profile.to_text()).to_equal("prod")
```

</details>

#### parses sdn

- parses sdn
   - Expected: profile.to_text() equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses sdn")
val profile = CompilerProfile.from_text("sdn")
expect(profile.to_text()).to_equal("sdn")
```

</details>

#### parses data alias

- parses data alias
   - Expected: profile.to_text() equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses data alias")
val profile = CompilerProfile.from_text("data")
expect(profile.to_text()).to_equal("sdn")
```

</details>

#### defaults unknown to Dev

- defaults unknown to Dev
   - Expected: profile.to_text() equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults unknown to Dev")
val profile = CompilerProfile.from_text("garbage")
expect(profile.to_text()).to_equal("dev")
```

</details>

#### round-trip

#### Dev round-trips through text

- Dev round-trips through text
   - Expected: restored.to_text() equals `dev`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Dev round-trips through text")
val original = CompilerProfile.Dev
val restored = CompilerProfile.from_text(original.to_text())
expect(restored.to_text()).to_equal("dev")
```

</details>

#### Prod round-trips through text

- Prod round-trips through text
   - Expected: restored.to_text() equals `prod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Prod round-trips through text")
val original = CompilerProfile.Prod
val restored = CompilerProfile.from_text(original.to_text())
expect(restored.to_text()).to_equal("prod")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `984976ba10a0330aa5257b166d9ce553883007835b519aadc3a4ec2fda61c76d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `984976ba10a0330aa5257b166d9ce553883007835b519aadc3a4ec2fda61c76d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `984976ba10a0330aa5257b166d9ce553883007835b519aadc3a4ec2fda61c76d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/config/compiler_profile_spec.spl
mirror: doc/06_spec/01_unit/compiler/config/compiler_profile_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/config/compiler_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/config/compiler_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/config/compiler_profile_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Dev to text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/config/compiler_profile_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Test to text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/config/compiler_profile_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Prod to text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
