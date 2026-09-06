# Sed Specification

> Tests covering sed tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sed Specification

## Scenarios

### sed tool

#### substitute parsing

#### parses basic substitute command

- parses basic substitute command
   - Expected: cmd.cmd_type equals `s`
   - Expected: cmd.pattern equals `hello`
   - Expected: cmd.replacement equals `world`
   - Expected: cmd.global_flag is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses basic substitute command")
val cmd = parse_substitute("s/hello/world/")
expect(cmd.cmd_type).to_equal("s")
expect(cmd.pattern).to_equal("hello")
expect(cmd.replacement).to_equal("world")
expect(cmd.global_flag).to_equal(false)
```

</details>

#### parses global substitute

- parses global substitute
   - Expected: cmd.cmd_type equals `s`
   - Expected: cmd.global_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses global substitute")
val cmd = parse_substitute("s/a/b/g")
expect(cmd.cmd_type).to_equal("s")
expect(cmd.global_flag).to_equal(true)
```

</details>

#### parses empty replacement

- parses empty replacement
   - Expected: cmd.cmd_type equals `s`
   - Expected: cmd.pattern equals `foo`
   - Expected: cmd.replacement equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty replacement")
val cmd = parse_substitute("s/foo//")
expect(cmd.cmd_type).to_equal("s")
expect(cmd.pattern).to_equal("foo")
expect(cmd.replacement).to_equal("")
```

</details>

#### script parsing

#### parses delete command

- parses delete command
   - Expected: cmd.cmd_type equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses delete command")
val cmd = parse_sed_script("d")
expect(cmd.cmd_type).to_equal("d")
```

</details>

#### parses print command

- parses print command
   - Expected: cmd.cmd_type equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses print command")
val cmd = parse_sed_script("p")
expect(cmd.cmd_type).to_equal("p")
```

</details>

#### parses quit command

- parses quit command
   - Expected: cmd.cmd_type equals `q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses quit command")
val cmd = parse_sed_script("q")
expect(cmd.cmd_type).to_equal("q")
```

</details>

#### command application

#### applies substitute

- applies substitute
   - Expected: result.0 equals `world there`
   - Expected: result.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies substitute")
val cmd = parse_substitute("s/hello/world/")
val result = apply_command("hello there", cmd)
expect(result.0).to_equal("world there")
expect(result.1).to_equal(true)
```

</details>

#### applies delete

- applies delete
   - Expected: result.1 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies delete")
val cmd = parse_sed_script("d")
val result = apply_command("line", cmd)
expect(result.1).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/sed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sed tool.
- sed tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `01356a05b9162867cc1d40cbde0bc62b288ce2a3fd8d0e48b2bb394290513caa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01356a05b9162867cc1d40cbde0bc62b288ce2a3fd8d0e48b2bb394290513caa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01356a05b9162867cc1d40cbde0bc62b288ce2a3fd8d0e48b2bb394290513caa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/sed_spec.spl
mirror: doc/06_spec/unit/tools/sed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/sed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/sed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/sed_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses basic substitute command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/sed_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses global substitute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/sed_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses empty replacement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
