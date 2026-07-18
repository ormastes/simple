# SMF Dynlib Checked Open Specification

> Verifies the lower SMF dynamic-library facade used by the low_dependency_ui_dynsmf checked startup path. The spec covers compatibility `smf_dlopen` behavior and checked artifact validation before a handle is reported as loaded.

<!-- sdn-diagram:id=smf_dynlib_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_dynlib_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_dynlib_spec -> std
smf_dynlib_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_dynlib_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = smf_dlopen(DynLoadRequest.lazy("file_io", "build/dynsmf/file_io.smf", "unit"), 42)
expect(ok.success).to_equal(true)
expect(ok.handle_id).to_equal(42)

val bad = smf_dlopen(DynLoadRequest.lazy("", "build/dynsmf/file_io.smf", "unit"), 42)
expect(bad.success).to_equal(false)
expect(bad.error_msg).to_equal("empty library name")
```

</details>

#### checked open accepts generated SMF artifacts

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build = ensure_low_dependency_dynsmf_artifacts()
expect(build.2).to_equal(0)

val opened = smf_dlopen_checked(DynLoadRequest.lazy("file_io", "build/dynsmf/file_io.smf", "unit"), 77)
expect(opened.success).to_equal(true)
expect(opened.handle_id).to_equal(77)
```

</details>

#### checked open rejects missing and non-SMF artifacts

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
