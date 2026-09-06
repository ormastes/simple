# Streaming Module Surface Lifecycle Specification

> Tests covering streaming module-surface driver lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Streaming Module Surface Lifecycle Specification

## Scenarios

### streaming module-surface driver lifecycle

#### preserves physical-source order and aliases through phase 2

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves physical-source order and aliases through phase 2
   - Expected: driver.ctx.modules.len() equals `0`
   - Expected: driver_surfaces.surfaces.len() equals `2`
   - Expected: surfaces.surfaces.len() equals `2`
   - Expected: surfaces.surfaces[0].module_name equals `fixture.alpha`
   - Expected: surfaces.index_by_name["fixture.alpha_alias"] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves physical-source order and aliases through phase 2")
var driver = streaming_driver()
val phase2_ok = driver.parse_all_committing_impl()
expect(phase2_ok).to_be(true)
expect(driver.ctx.modules.len()).to_equal(0)
expect(driver.ctx.module_surfaces != nil).to_be(true)
expect(driver.streaming_module_surfaces_owner != nil).to_be(true)
val driver_surfaces = driver.streaming_module_surfaces_owner.unwrap()
expect(driver_surfaces.surfaces.len()).to_equal(2)
val surfaces = driver.ctx.module_surfaces.unwrap()
expect(surfaces.surfaces.len()).to_equal(2)
expect(surfaces.surfaces[0].module_name).to_equal("fixture.alpha")
expect(surfaces.index_by_name["fixture.alpha_alias"]).to_equal(0)
```

</details>

#### dispatches from stable streaming state when readiness flag is lost

- dispatches from stable streaming state when readiness flag is lost
   - Expected: phase3_ctx.modules.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches from stable streaming state when readiness flag is lost")
var driver = streaming_driver()
val phase2_ok = driver.parse_all_committing_impl()
expect(phase2_ok).to_be(true)
# Reproduce the native phase-boundary value-semantics failure: the
# frozen owner remains in CompileContext while the adjacent flag is
# reset. Production dispatch must still select the streaming path.
driver.streaming_surface_owner_ready = false
val (phase3_ctx, phase3_ok) = driver.lower_and_check_impl()
expect(phase3_ok).to_be(true)
expect(phase3_ctx.modules.keys().len()).to_equal(0)
expect(phase3_ctx.hir_modules.contains_key("fixture.alpha")).to_be(true)
expect(phase3_ctx.hir_modules.contains_key("fixture.alpha_alias")).to_be(true)
expect(phase3_ctx.hir_modules.contains_key("fixture.beta")).to_be(true)
expect(phase3_ctx.hir_modules["fixture.alpha"].functions.keys().len()).to_be_greater_than(0)
expect(phase3_ctx.hir_modules["fixture.alpha_alias"].functions.keys().len()).to_be_greater_than(0)
expect(phase3_ctx.hir_modules["fixture.beta"].functions.keys().len()).to_be_greater_than(0)
```

</details>

#### retains source and surface state after a phase-3 fingerprint failure

- retains source and surface state after a phase-3 fingerprint failure
   - Expected: driver.ctx.sources.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains source and surface state after a phase-3 fingerprint failure")
var driver = streaming_driver()
val phase2_ok = driver.parse_all_committing_impl()
expect(phase2_ok).to_be(true)
var sources = driver.ctx.sources
sources[0] = streaming_source("build/streaming/alpha.spl", "fn alpha() -> i64:\n    return 99\n", "fixture.alpha")
driver.ctx.sources = sources
val (_, phase3_ok) = driver.lower_and_check_streaming_surfaces_impl()
expect(phase3_ok).to_be(false)
expect(driver.ctx.sources.len()).to_equal(3)
expect(driver.ctx.module_surfaces != nil).to_be(true)
expect(driver.ctx.errors[0]).to_contain("fingerprint mismatch")
```

</details>

#### fails cleanly when readiness survives but the optional owner is absent

- fails cleanly when readiness survives but the optional owner is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails cleanly when readiness survives but the optional owner is absent")
var driver = streaming_driver()
driver.streaming_surface_owner_ready = true
driver.streaming_module_surfaces_owner = nil
val (_, phase3_ok) = driver.lower_and_check_streaming_surfaces_impl()
expect(phase3_ok).to_be(false)
expect(driver.ctx.errors.len()).to_be_greater_than(0)
expect(driver.ctx.errors[0]).to_contain(
    "Streaming module surfaces missing after phase 2")
```

</details>

#### fails cleanly when Some carries a nil surface payload

- fails cleanly when Some carries a nil surface payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails cleanly when Some carries a nil surface payload")
var driver = streaming_driver()
driver.streaming_surface_owner_ready = true
driver.streaming_module_surfaces_owner = Some(nil)
val (_, phase3_ok) = driver.lower_and_check_streaming_surfaces_impl()
expect(phase3_ok).to_be(false)
expect(driver.ctx.errors.len()).to_be_greater_than(0)
expect(driver.ctx.errors[0]).to_contain(
    "Streaming module surface owner payload missing after phase 2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering streaming module-surface driver lifecycle.
- streaming module-surface driver lifecycle

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

- Canonical SPipe generation for source `99c2a5b84ee3c180a3c117d1c69160b33799d7c8bdec65dee6140bba18fe68ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99c2a5b84ee3c180a3c117d1c69160b33799d7c8bdec65dee6140bba18fe68ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99c2a5b84ee3c180a3c117d1c69160b33799d7c8bdec65dee6140bba18fe68ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves physical-source order and aliases through phase 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches from stable streaming state when readiness flag is lost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/streaming_module_surface_lifecycle_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains source and surface state after a phase-3 fingerprint failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
