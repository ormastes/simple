# Simpleos Wm Theme Bootstrap Specification

> Tests covering SimpleOS generated WM theme bootstrap.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wm Theme Bootstrap Specification

## Scenarios

### SimpleOS generated WM theme bootstrap

#### returns and applies the generated Fluid OS snapshot

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns and applies the generated Fluid OS snapshot
   - Expected: installed.id equals `expected.id`
   - Expected: installed.source_manifest_sha256 equals `expected.source_manifest_sha256`
   - Expected: installed.material_sha256 equals `expected.material_sha256`
   - Expected: active.id equals `expected.id`
   - Expected: active.material_sha256 equals `expected.material_sha256`
   - Expected: wm_chrome_theme().compositor_bg equals `expected.material.desktop_fill_rgba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns and applies the generated Fluid OS snapshot")
reset_wm_chrome_theme()
val expected = fluid_light_theme_render_snapshot()
val installed = install_generated_simpleos_wm_theme()
expect(installed.id).to_equal(expected.id)
expect(installed.source_manifest_sha256).to_equal(expected.source_manifest_sha256)
expect(installed.material_sha256).to_equal(expected.material_sha256)
expect(active_wm_theme_snapshot_present()).to_be(true)
val active = active_wm_theme_snapshot_unchecked()
expect(active.id).to_equal(expected.id)
expect(active.material_sha256).to_equal(expected.material_sha256)
expect(wm_chrome_theme().compositor_bg).to_equal(expected.material.desktop_fill_rgba)
reset_wm_chrome_theme()
```

</details>

#### preserves package semantic colors through the generated bootstrap snapshot

- preserves package semantic colors through the generated bootstrap snapshot
- Compare every generated semantic role with the registered Fluid package
- Resolve named Fluid semantic roles through the WM projection


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves package semantic colors through the generated bootstrap snapshot")
reset_wm_chrome_theme()
val package_snapshot = theme_package_render_snapshot("fluid_light")
val installed = install_generated_simpleos_wm_theme()

step("Compare every generated semantic role with the registered Fluid package")
expect(installed.semantic.info_rgba == package_snapshot.semantic.info_rgba).to_be(true)
expect(installed.semantic.success_rgba == package_snapshot.semantic.success_rgba).to_be(true)
expect(installed.semantic.warning_rgba == package_snapshot.semantic.warning_rgba).to_be(true)
expect(installed.semantic.error_rgba == package_snapshot.semantic.error_rgba).to_be(true)

step("Resolve named Fluid semantic roles through the WM projection")
expect(theme_role_color(installed, "semantic.info").rgba == 0xFF0070EBu32).to_be(true)
expect(theme_role_color(installed, "semantic.error").rgba == 0xFFBA1A1Au32).to_be(true)
reset_wm_chrome_theme()
```

</details>

#### derives the active snapshot when mounted CSS overrides the generated palette

- derives the active snapshot when mounted CSS overrides the generated palette
   - Expected: effective.id equals `generated.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("derives the active snapshot when mounted CSS overrides the generated palette")
reset_wm_chrome_theme()
val generated = install_generated_simpleos_wm_theme()
val css = "--wm-bg: #0f172a; --wm-fg: #f8fafc; --wm-accent: #2050a0; --wm-surface: #1e293b; --wm-surface-hover: #334155; --wm-error: #dc2626;"

expect(apply_simpleos_css_theme_override(css)).to_be(true)
val effective = active_wm_theme_snapshot_unchecked()

expect(effective.id).to_equal(generated.id)
expect(effective.material_sha256 == generated.material_sha256).to_be(false)
expect(effective.material.desktop_fill_rgba == 0xFF0F172Au32).to_be(true)
expect(effective.material.text_rgba == 0xFFF8FAFCu32).to_be(true)
expect(effective.material.window_fill_rgba == 0xFF1E293Bu32).to_be(true)
expect(wm_chrome_theme().close_button == 0xFFDC2626u32).to_be(true)
reset_wm_chrome_theme()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS generated WM theme bootstrap.
- SimpleOS generated WM theme bootstrap

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b8b5527fa4e676ac6a5ee33364cabf5011e899fb47d15d1a2d1cd41e3764e2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b8b5527fa4e676ac6a5ee33364cabf5011e899fb47d15d1a2d1cd41e3764e2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b8b5527fa4e676ac6a5ee33364cabf5011e899fb47d15d1a2d1cd41e3764e2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns and applies the generated Fluid OS snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves package semantic colors through the generated bootstrap snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/simpleos_wm_theme_bootstrap_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives the active snapshot when mounted CSS overrides the generated palette' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
