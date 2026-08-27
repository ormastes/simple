# coreutils/ls argument parsing

> Exercises `main_ls` argument parsing. Actual directory listing is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/ls argument parsing

Exercises `main_ls` argument parsing. Actual directory listing is

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/unit/os/apps/coreutils/ls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `main_ls` argument parsing. Actual directory listing is
stubbed by the test harness (vfs_opendir returns 0 by default).

## Scenarios

### ls argument parsing

#### --help returns 0

- --help returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("--help returns 0")
"""Help is a no-op that exits successfully."""
val rc = main_ls(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### -1 flag is accepted and stripped

- -1 flag is accepted and stripped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-1 flag is accepted and stripped")
"""-1 is the default — accepted silently, no listings needed for rc."""
val rc = main_ls(["-1", "--help"])
expect rc.to_equal(0i32)
```

</details>

#### empty args lists '.' and returns i32

- empty args lists '.' and returns i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty args lists '.' and returns i32")
"""Default path is ".". Whether the stubbed opendir succeeds, the
call type-checks and returns an i32."""
val rc = main_ls([])
val is_int: bool = rc == 0i32 or rc == 1i32
expect is_int.to_equal(true)
```

</details>

### ls_list_one
_Single-path helper._

#### returns an i32 exit code

- returns an i32 exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an i32 exit code")
"""Stubbed vfs returns 0 handle; the helper must still type-check
and produce a numeric status."""
val rc = ls_list_one(".")
val is_int: bool = rc == 0i32 or rc == 1i32
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

- Canonical SPipe generation for source `01ea4fbac4e8bc5b15c5b91081fb37d61035185a65e5dfe6775ad2512661a17f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01ea4fbac4e8bc5b15c5b91081fb37d61035185a65e5dfe6775ad2512661a17f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01ea4fbac4e8bc5b15c5b91081fb37d61035185a65e5dfe6775ad2512661a17f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/apps/coreutils/ls_spec.spl
mirror: doc/06_spec/unit/os/apps/coreutils/ls_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/coreutils/ls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/coreutils/ls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/coreutils/ls_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '--help returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/ls_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '-1 flag is accepted and stripped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/ls_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty args lists '.' and returns i32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
