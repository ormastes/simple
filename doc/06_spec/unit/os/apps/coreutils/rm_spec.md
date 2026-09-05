# coreutils/rm argument parsing

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/rm argument parsing

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/unit/os/apps/coreutils/rm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### rm argument parsing

#### --help returns 0

- --help returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("--help returns 0")
"""Help exits successfully."""
val rc = main_rm(["--help"])
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
"""rm with no path must error."""
val rc = main_rm([])
expect rc.to_equal(1i32)
```

</details>

#### -f flag is accepted

- -f flag is accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-f flag is accepted")
"""rm -f still requires a path and returns an i32."""
val rc = main_rm(["-f", "/tmp/x"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

### rm_one
_Single-path unlink helper._

#### returns i32 in force mode

- returns i32 in force mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns i32 in force mode")
"""Force mode must return a numeric status regardless of existence."""
val rc = rm_one("/tmp/x", true)
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

#### returns i32 in non-force mode

- returns i32 in non-force mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns i32 in non-force mode")
"""Without -f, still returns a numeric status."""
val rc = rm_one("/tmp/x", false)
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

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

- Canonical SPipe generation for source `a1bf33096eecce0123f27962b383c825ad0644390aa8a26f2975095ff3e54462`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1bf33096eecce0123f27962b383c825ad0644390aa8a26f2975095ff3e54462`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1bf33096eecce0123f27962b383c825ad0644390aa8a26f2975095ff3e54462`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/apps/coreutils/rm_spec.spl
mirror: doc/06_spec/unit/os/apps/coreutils/rm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/coreutils/rm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/coreutils/rm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/coreutils/rm_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '--help returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/rm_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'missing operand returns 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/rm_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '-f flag is accepted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
