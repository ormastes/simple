# Theme Package Wire Native Abi Probe Specification

> Tests covering theme package wire native aggregate ABI admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Theme Package Wire Native Abi Probe Specification

## Scenarios

### theme package wire native aggregate ABI admission

#### returns a complete snapshot aggregate across the module boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = aetheric_dark_theme_render_snapshot()
match theme_render_snapshot_wire_v1_encode(source):
    Err(_error):
        expect(false).to_equal(true)
    Ok(wire):
        match theme_render_snapshot_wire_v1_decode(wire):
            Err(_error):
                expect(false).to_equal(true)
            Ok(decoded):
                expect(decoded.id).to_equal(source.id)
                expect(decoded.material_sha256).to_equal(source.material_sha256)
                expect(decoded.material.active_shadows.len()).to_equal(source.material.active_shadows.len())
                expect(decoded.material.inactive_shadows.len()).to_equal(source.material.inactive_shadows.len())
                expect(decoded.material.window_gradient_source_css).to_equal(source.material.window_gradient_source_css)
                match theme_render_snapshot_wire_v1_encode(decoded):
                    Err(_error):
                        expect(false).to_equal(true)
                    Ok(reencoded):
                        expect(reencoded).to_equal(wire)
```

</details>

#### returns install metadata and nested snapshot aggregates across the module boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = aetheric_dark_theme_render_snapshot()
match theme_package_install_wire_v1_encode("aetheric_dark", "aetheric_dark", "config/themes/theme.sdn", source):
    Err(_error):
        expect(false).to_equal(true)
    Ok(wire):
        match theme_package_install_wire_v1_decode(wire):
            Err(_error):
                expect(false).to_equal(true)
            Ok(projection):
                expect(projection.requested_id).to_equal("aetheric_dark")
                expect(projection.default_id).to_equal("aetheric_dark")
                expect(projection.registry_path).to_equal("config/themes/theme.sdn")
                expect(projection.snapshot.id).to_equal(source.id)
                expect(projection.snapshot.material_sha256).to_equal(source.material_sha256)
                match theme_package_install_wire_v1_encode(projection.requested_id, projection.default_id, projection.registry_path, projection.snapshot):
                    Err(_error):
                        expect(false).to_equal(true)
                    Ok(reencoded):
                        expect(reencoded).to_equal(wire)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering theme package wire native aggregate ABI admission.
- theme package wire native aggregate ABI admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8a9dc47701c8d4f2e19a63fe30baf61a13c210489eedf84c87eb84cd390e48f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8a9dc47701c8d4f2e19a63fe30baf61a13c210489eedf84c87eb84cd390e48f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8a9dc47701c8d4f2e19a63fe30baf61a13c210489eedf84c87eb84cd390e48f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.md (current)
findings: 8 blockers: 0
  narrative=80 structure=80 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl:17:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns a complete snapshot aggregate across the module boundary' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns install metadata and nested snapshot aggregates across the module boundary' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
