# SMF Dynlib Checked Open Specification

> Verifies the smf dynlib behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF Dynlib Checked Open Specification

Verifies the smf dynlib behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the smf dynlib behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SMF dynlib checked open

#### keeps compatibility open shape validation

- Verify: keeps compatibility open shape validation
   - Expected: ok.success is true
   - Expected: ok.handle_id equals `42)  # oracle: pinned constant asserted by this scenario`
   - Expected: bad.success is false
   - Expected: bad.error_msg equals `empty library name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-009 REQ-010
step("Verify: keeps compatibility open shape validation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ok = smf_dlopen(DynLoadRequest.lazy("file_io", "build/dynsmf/file_io.smf", "unit"), 42)
expect(ok.success).to_equal(true)
expect(ok.handle_id).to_equal(42)  # oracle: pinned constant asserted by this scenario

val bad = smf_dlopen(DynLoadRequest.lazy("", "build/dynsmf/file_io.smf", "unit"), 42)
expect(bad.success).to_equal(false)
expect(bad.error_msg).to_equal("empty library name")
```

</details>

#### checked open accepts generated SMF artifacts

- Verify: checked open accepts generated SMF artifacts
   - Expected: build.2 equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: opened.success is true
   - Expected: opened.handle_id equals `77)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-009 REQ-010
step("Verify: checked open accepts generated SMF artifacts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val build = ensure_low_dependency_dynsmf_artifacts()
expect(build.2).to_equal(0)  # oracle: pinned constant asserted by this scenario

val opened = smf_dlopen_checked(DynLoadRequest.lazy("file_io", "build/dynsmf/file_io.smf", "unit"), 77)
expect(opened.success).to_equal(true)
expect(opened.handle_id).to_equal(77)  # oracle: pinned constant asserted by this scenario
```

</details>

#### checked open rejects missing and non-SMF artifacts

- Verify: checked open rejects missing and non-SMF artifacts
   - Expected: missing.success is false
   - Expected: missing.error_msg equals `artifact missing`
   - Expected: wrong_ext.success is false
   - Expected: wrong_ext.error_msg equals `not an smf artifact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-009 REQ-010
step("Verify: checked open rejects missing and non-SMF artifacts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- **Requirements:** `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- **Plan:** `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md`
- **Design:** `doc/05_design/low_dependency_ui_dynsmf.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c6b6b1f7f9ca0ab9599d846aa49ea257c386e201f9ca8b44802c227b2d292cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c6b6b1f7f9ca0ab9599d846aa49ea257c386e201f9ca8b44802c227b2d292cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c6b6b1f7f9ca0ab9599d846aa49ea257c386e201f9ca8b44802c227b2d292cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/smf/smf_dynlib_spec.spl
mirror: doc/06_spec/01_unit/os/smf/smf_dynlib_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/smf/smf_dynlib_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/smf/smf_dynlib_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/smf/smf_dynlib_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
