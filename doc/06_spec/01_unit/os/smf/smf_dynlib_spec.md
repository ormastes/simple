# SMF Dynlib Checked Open Specification

> Verifies the lower SMF dynamic-library facade used by the low_dependency_ui_dynsmf checked startup path. The spec covers compatibility `smf_dlopen` behavior and checked artifact validation before a handle is reported as loaded.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF Dynlib Checked Open Specification

Verifies the lower SMF dynamic-library facade used by the low_dependency_ui_dynsmf checked startup path. The spec covers compatibility `smf_dlopen` behavior and checked artifact validation before a handle is reported as loaded.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/01_unit/os/smf/smf_dynlib_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the lower SMF dynamic-library facade used by the
low_dependency_ui_dynsmf checked startup path. The spec covers compatibility
`smf_dlopen` behavior and checked artifact validation before a handle is
reported as loaded.

## Examples

The compatibility open path validates request shape only. The checked open path
requires a generated `.smf` artifact with `SMF\0` magic and fails deterministically
for missing or non-SMF artifact paths.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-005, REQ-009, REQ-010, NFR-005, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### SMF dynlib checked open

#### keeps compatibility open shape validation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps compatibility open shape validation
   - Expected: ok.success is true
   - Expected: ok.handle_id equals `42`
   - Expected: bad.success is false
   - Expected: bad.error_msg equals `empty library name`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps compatibility open shape validation")
val ok = smf_dlopen(DynLoadRequest.lazy("file_io", "build/dynsmf/file_io.smf", "unit"), 42)
expect(ok.success).to_equal(true)
expect(ok.handle_id).to_equal(42)

val bad = smf_dlopen(DynLoadRequest.lazy("", "build/dynsmf/file_io.smf", "unit"), 42)
expect(bad.success).to_equal(false)
expect(bad.error_msg).to_equal("empty library name")
```

</details>

#### checked open accepts generated SMF artifacts

- checked open accepts generated SMF artifacts
   - Expected: build.2 equals `0`
   - Expected: opened.success is true
   - Expected: opened.handle_id equals `77`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("checked open accepts generated SMF artifacts")
val build = ensure_low_dependency_dynsmf_artifacts()
expect(build.2).to_equal(0)

val opened = smf_dlopen_checked(DynLoadRequest.lazy("file_io", "build/dynsmf/file_io.smf", "unit"), 77)
expect(opened.success).to_equal(true)
expect(opened.handle_id).to_equal(77)
```

</details>

#### checked open rejects missing and non-SMF artifacts

- checked open rejects missing and non-SMF artifacts
   - Expected: missing.success is false
   - Expected: missing.error_msg equals `artifact missing`
   - Expected: wrong_ext.success is false
   - Expected: wrong_ext.error_msg equals `not an smf artifact`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("checked open rejects missing and non-SMF artifacts")
val missing = smf_dlopen_checked(DynLoadRequest.lazy("missing", "build/dynsmf/not_present_for_smf_dynlib_spec.smf", "unit"), 88)
expect(missing.success).to_equal(false)
expect(missing.error_msg).to_equal("artifact missing")

val wrong_ext = smf_dlopen_checked(DynLoadRequest.lazy("wrong", "build/dynsmf/file_io.txt", "unit"), 89)
expect(wrong_ext.success).to_equal(false)
expect(wrong_ext.error_msg).to_equal("not an smf artifact")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-005`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `244e74d148e2aa59e084920151ab54cc940e0903218377206a5a890e85e8790b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `244e74d148e2aa59e084920151ab54cc940e0903218377206a5a890e85e8790b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `244e74d148e2aa59e084920151ab54cc940e0903218377206a5a890e85e8790b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/smf/smf_dynlib_spec.spl
mirror: doc/06_spec/01_unit/os/smf/smf_dynlib_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/smf/smf_dynlib_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/smf/smf_dynlib_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/smf/smf_dynlib_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/smf/smf_dynlib_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps compatibility open shape validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smf/smf_dynlib_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checked open accepts generated SMF artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/smf/smf_dynlib_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checked open rejects missing and non-SMF artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
