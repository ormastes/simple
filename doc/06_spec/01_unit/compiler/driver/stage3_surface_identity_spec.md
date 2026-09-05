# Stage3 Surface Identity Specification

> Tests covering Stage3 surface validation identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage3 Surface Identity Specification

## Scenarios

### Stage3 surface validation identity

#### accepts the exact physical source identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the exact physical source identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the exact physical source identity")
val path = rt_path_absolute("src/app/cli/bootstrap_main.spl")
expect(driver_stage3_surface_identity_matches(
    0, path, "app.cli.bootstrap_main", 17, 991,
    0, "src/app/cli/bootstrap_main.spl",
    "app.cli.bootstrap_main", 17, 991)).to_be(true)
```

</details>

#### rejects a same-index alias with a different physical path

- rejects a same-index alias with a different physical path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a same-index alias with a different physical path")
val other = rt_path_absolute("src/compiler/80.driver/driver.spl")
expect(driver_stage3_surface_identity_matches(
    0, other, "app.cli.bootstrap_main", 17, 991,
    0, "src/app/cli/bootstrap_main.spl",
    "app.cli.bootstrap_main", 17, 991)).to_be(false)
```

</details>

#### rejects stale source content and module identity

- rejects stale source content and module identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects stale source content and module identity")
val path = rt_path_absolute("src/app/cli/bootstrap_main.spl")
expect(driver_stage3_surface_identity_matches(
    0, path, "compiler.driver.driver", 17, 990,
    0, "src/app/cli/bootstrap_main.spl",
    "app.cli.bootstrap_main", 17, 991)).to_be(false)
```

</details>

#### accepts a compatibility alias only for identical physical content

- accepts a compatibility alias only for identical physical content


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a compatibility alias only for identical physical content")
val path = rt_path_absolute("src/compiler/10.frontend/core/aop.spl")
expect(driver_stage3_surface_content_matches(
    path, 25391, 0,
    "src/compiler/10.frontend/core/aop.spl", 25391, 0)).to_be(true)
expect(driver_stage3_surface_content_matches(
    path, 25391, 0,
    "src/compiler/10.frontend/core/aop.spl", 25392, 0)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/stage3_surface_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage3 surface validation identity.
- Stage3 surface validation identity

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

- Canonical SPipe generation for source `5cc08510bd31c692fed6d670a595bb818e147f316a51ee03fbf7a9e50705e62d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5cc08510bd31c692fed6d670a595bb818e147f316a51ee03fbf7a9e50705e62d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5cc08510bd31c692fed6d670a595bb818e147f316a51ee03fbf7a9e50705e62d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/stage3_surface_identity_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/stage3_surface_identity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/stage3_surface_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/stage3_surface_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/stage3_surface_identity_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the exact physical source identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/stage3_surface_identity_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a same-index alias with a different physical path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/stage3_surface_identity_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale source content and module identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
