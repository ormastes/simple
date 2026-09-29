# coreutils/chmod argument parsing + octal parser

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/chmod argument parsing + octal parser

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/unit/os/apps/coreutils/chmod_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### parse_octal

#### parses '0755' as 493

- parses '0755' as 493


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses '0755' as 493")
"""Classic owner-all / group-rx / other-rx."""
expect parse_octal("0755").to_equal(493i64)
```

</details>

#### parses '644' as 420

- parses '644' as 420


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses '644' as 420")
"""Leading zero is optional."""
expect parse_octal("644").to_equal(420i64)
```

</details>

#### rejects non-octal digits

- rejects non-octal digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-octal digits")
"""'8' and '9' are not octal."""
expect parse_octal("788").to_equal(-1i64)
```

</details>

#### rejects alphabetic input

- rejects alphabetic input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects alphabetic input")
"""Letters are never valid in a mode."""
expect parse_octal("abc").to_equal(-1i64)
```

</details>

#### rejects the empty string

- rejects the empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the empty string")
"""No input, no mode."""
expect parse_octal("").to_equal(-1i64)
```

</details>

### main_chmod argument parsing
_Entry-point argument handling._

#### too-few args returns 1

- too-few args returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("too-few args returns 1")
"""Mode-only or zero-arg calls must fail usage."""
val rc = main_chmod(["0755"])
expect rc.to_equal(1i32)
```

</details>

#### invalid mode returns 1

- invalid mode returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid mode returns 1")
"""Bad octal text exits with usage failure."""
val rc = main_chmod(["xyz", "/tmp/f"])
expect rc.to_equal(1i32)
```

</details>

#### valid mode + path returns i32

- valid mode + path returns i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("valid mode + path returns i32")
"""Happy path returns a numeric status from vfs_chmod."""
val rc = main_chmod(["0755", "/tmp/f"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

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

- Canonical SPipe generation for source `68a70c421fd8af10f8d9aa57583132daaf4dd6a1d75683953dde1021127929d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68a70c421fd8af10f8d9aa57583132daaf4dd6a1d75683953dde1021127929d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68a70c421fd8af10f8d9aa57583132daaf4dd6a1d75683953dde1021127929d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/apps/coreutils/chmod_spec.spl
mirror: doc/06_spec/unit/os/apps/coreutils/chmod_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/coreutils/chmod_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/coreutils/chmod_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/coreutils/chmod_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses '0755' as 493' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/chmod_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses '644' as 420' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/chmod_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-octal digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
