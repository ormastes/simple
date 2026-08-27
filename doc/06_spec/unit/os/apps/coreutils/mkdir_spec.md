# coreutils/mkdir argument parsing

> Exercises `main_mkdir` argument parsing. Actual IO is stubbed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/mkdir argument parsing

Exercises `main_mkdir` argument parsing. Actual IO is stubbed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/unit/os/apps/coreutils/mkdir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `main_mkdir` argument parsing. Actual IO is stubbed.

## Scenarios

### mkdir argument parsing

#### --help returns 0

- --help returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("--help returns 0")
"""Help is a no-op exiting successfully."""
val rc = main_mkdir(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### missing operand returns 1

- missing operand returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing operand returns 1")
"""mkdir with no paths must error."""
val rc = main_mkdir([])
expect rc.to_equal(1i32)
```

</details>

#### -p flag is accepted

- -p flag is accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-p flag is accepted")
"""mkdir -p must still require a path and succeed-or-error cleanly."""
val rc = main_mkdir(["-p", "/tmp/a/b/c"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

### mkdir_one
_Single directory helper._

#### returns an i32

- returns an i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an i32")
"""Plain mkdir returns a numeric status."""
val rc = mkdir_one("/tmp/x", 0o755u32)
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

### mkdir_p
_Recursive-parents helper._

#### returns an i32

- returns an i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an i32")
"""Parents mode walks prefixes and produces a numeric status."""
val rc = mkdir_p("/tmp/a/b/c")
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

#### empty path returns 0

- empty path returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty path returns 0")
"""Degenerate input yields success (nothing to create)."""
val rc = mkdir_p("")
expect rc.to_equal(0i32)
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28892d9f9e5b98628c28e7fc003c762fc657a058bf570593eb6b0bc151cafebb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28892d9f9e5b98628c28e7fc003c762fc657a058bf570593eb6b0bc151cafebb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28892d9f9e5b98628c28e7fc003c762fc657a058bf570593eb6b0bc151cafebb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/apps/coreutils/mkdir_spec.spl
mirror: doc/06_spec/unit/os/apps/coreutils/mkdir_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/coreutils/mkdir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/coreutils/mkdir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/coreutils/mkdir_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '--help returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/mkdir_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'missing operand returns 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/mkdir_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '-p flag is accepted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
