# Rt Dir List Header No Collision Specification

> Tests covering rt_dir_list platform-header collision (repro), same defect class: renamed private workers stay renamed (generalization).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rt Dir List Header No Collision Specification

## Scenarios

### rt_dir_list platform-header collision (repro)

#### unix_common.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- unix_common.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unix_common.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list")
val src = header("unix_common.h")
expect(src).to_contain("rt_dir_list_cpath(const char*")
assert_false(src.contains("** rt_dir_list(const char*"))
```

</details>

#### platform_win.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list

- platform_win.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("platform_win.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list")
val src = header("platform_win.h")
expect(src).to_contain("rt_dir_list_cpath(const char*")
assert_false(src.contains("** rt_dir_list(const char*"))
```

</details>

### same defect class: renamed private workers stay renamed (generalization)

#### headers were actually read (non-vacuous control)

- headers were actually read (non-vacuous control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("headers were actually read (non-vacuous control)")
assert_true(header("unix_common.h").contains("rt_dir_list_cpath"))
assert_true(header("platform_win.h").contains("rt_dir_list_cpath"))
```

</details>

#### rt_dir_list_free keeps its distinct name in both headers

- rt_dir_list_free keeps its distinct name in both headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_dir_list_free keeps its distinct name in both headers")
assert_true(header("unix_common.h").contains("rt_dir_list_free(const char**"))
assert_true(header("platform_win.h").contains("rt_dir_list_free(const char**"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/unit/runtime/rt_dir_list_header_no_collision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_dir_list platform-header collision (repro), same defect class: renamed private workers stay renamed (generalization).
- rt_dir_list platform-header collision (repro)
- same defect class: renamed private workers stay renamed (generalization)

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

- Canonical SPipe generation for source `e4f6afedd85e1c6ca1516c163d079a2e8ce78cf03c4ccbbf9c049a0f48a2c37c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4f6afedd85e1c6ca1516c163d079a2e8ce78cf03c4ccbbf9c049a0f48a2c37c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4f6afedd85e1c6ca1516c163d079a2e8ce78cf03c4ccbbf9c049a0f48a2c37c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/runtime/rt_dir_list_header_no_collision_spec.spl
mirror: doc/06_spec/unit/runtime/rt_dir_list_header_no_collision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/runtime/rt_dir_list_header_no_collision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/runtime/rt_dir_list_header_no_collision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/runtime/rt_dir_list_header_no_collision_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unix_common.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/runtime/rt_dir_list_header_no_collision_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'platform_win.h names the private C-string worker rt_dir_list_cpath, not rt_dir_list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/runtime/rt_dir_list_header_no_collision_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'headers were actually read (non-vacuous control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
