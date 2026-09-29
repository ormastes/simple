# Project Sdn Profile Specification

> Tests covering simple.sdn lints.profile pins the project profile.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Project Sdn Profile Specification

## Scenarios

### simple.sdn lints.profile pins the project profile

#### resolves the canonical indent/colon form to critical

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves the canonical indent/colon form to critical
- load the fixture project root that carries the lints.profile key
   - Expected: ctx.active_profile ?? "" equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves the canonical indent/colon form to critical")
"""A manifest with `lints:` / `  profile: critical` pins critical."""
step("load the fixture project root that carries the lints.profile key")
val ctx = ProjectContext.from_root(WITH_ROOT)
expect(ctx.active_profile ?? "").to_equal("critical")
```

</details>

#### leaves the profile unpinned when the key is absent

- leaves the profile unpinned when the key is absent
- load the fixture project root that omits the lints section
   - Expected: ctx.active_profile ?? "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves the profile unpinned when the key is absent")
"""The same loader on a manifest with no `lints:` section pins nothing."""
step("load the fixture project root that omits the lints section")
val ctx = ProjectContext.from_root(WITHOUT_ROOT)
expect(ctx.active_profile ?? "").to_equal("")
```

</details>

#### makes the two fixtures differ

- makes the two fixtures differ
- compare both roots in one example so a fail-open cannot hide
   - Expected: pinned == unpinned is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("makes the two fixtures differ")
"""The with-key and without-key results are not the same value."""
step("compare both roots in one example so a fail-open cannot hide")
val pinned = ProjectContext.from_root(WITH_ROOT).active_profile ?? ""
val unpinned = ProjectContext.from_root(WITHOUT_ROOT).active_profile ?? ""
expect(pinned == unpinned).to_equal(false)
```

</details>

#### maps the project name out of the manifest

- maps the project name out of the manifest
- read project.name from the parsed manifest
   - Expected: ctx.name equals `aero_fixture_project`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps the project name out of the manifest")
"""Field mapping is real, not a defaults passthrough."""
# The fixture's project.name is deliberately NOT the directory basename
# ("with_profile"): with_defaults() derives the name from the basename,
# so a matching name would make this example pass without any mapping.
step("read project.name from the parsed manifest")
val ctx = ProjectContext.from_root(WITH_ROOT)
expect(ctx.name).to_equal("aero_fixture_project")
```

</details>

#### parses the canonical nested form into a dotted-path-addressable value

- parses the canonical nested form into a dotted-path-addressable value
- parse the fixture text and address lints.profile by dotted path
   - Expected: (v.get_path("lints.profile") ?? SdnValue.Null).as_str() ?? "" equals `critical`
   - Expected: "parse failed: {e}" equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses the canonical nested form into a dotted-path-addressable value")
"""The SDN parser itself handles indent-nested block mappings."""
step("parse the fixture text and address lints.profile by dotted path")
val parsed = parse(file_read("{WITH_ROOT}/simple.sdn"))
match parsed:
    case Ok(v):
        expect((v.get_path("lints.profile") ?? SdnValue.Null).as_str() ?? "").to_equal("critical")
    case Err(e):
        expect("parse failed: {e}").to_equal("Ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/project_sdn_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple.sdn lints.profile pins the project profile.
- simple.sdn lints.profile pins the project profile

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f485fdb6b109b98d5fc2dabda880afdf02c6aaf943de2c0a87f041815ce0034d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f485fdb6b109b98d5fc2dabda880afdf02c6aaf943de2c0a87f041815ce0034d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f485fdb6b109b98d5fc2dabda880afdf02c6aaf943de2c0a87f041815ce0034d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/project_sdn_profile_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/project_sdn_profile_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/project_sdn_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/project_sdn_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/project_sdn_profile_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the canonical indent/colon form to critical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/project_sdn_profile_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves the profile unpinned when the key is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/project_sdn_profile_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes the two fixtures differ' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
