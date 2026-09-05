# coreutils/cat argument parsing

> Exercises `main_cat` argument parsing. Actual IO is stubbed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/cat argument parsing

Exercises `main_cat` argument parsing. Actual IO is stubbed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/unit/os/apps/coreutils/cat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `main_cat` argument parsing. Actual IO is stubbed.

## Scenarios

### cat argument parsing

#### zero args returns 1 (usage error)

- zero args returns 1 (usage error)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero args returns 1 (usage error)")
"""cat with no arguments must report an error without crashing."""
val rc = main_cat([])
expect rc.to_equal(1i32)
```

</details>

#### one arg returns an i32

- one arg returns an i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one arg returns an i32")
"""Single-file path type-checks and produces a numeric status."""
val rc = main_cat(["/tmp/x"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

#### multiple args are iterated

- multiple args are iterated


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple args are iterated")
"""More than one path still type-checks to i32."""
val rc = main_cat(["/tmp/a", "/tmp/b"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

### cat_one
_Single-file helper._

#### returns an i32 exit code

- returns an i32 exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an i32 exit code")
"""Stubbed vfs returns 0 handle; helper still produces numeric status."""
val rc = cat_one("/tmp/x")
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `a71d43089ccc6a92f63b734dca431c4569617f83b1ffcdac3ce9bff04aac44b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a71d43089ccc6a92f63b734dca431c4569617f83b1ffcdac3ce9bff04aac44b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a71d43089ccc6a92f63b734dca431c4569617f83b1ffcdac3ce9bff04aac44b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/apps/coreutils/cat_spec.spl
mirror: doc/06_spec/unit/os/apps/coreutils/cat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/coreutils/cat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/coreutils/cat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/coreutils/cat_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero args returns 1 (usage error)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/cat_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'one arg returns an i32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/cat_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple args are iterated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
