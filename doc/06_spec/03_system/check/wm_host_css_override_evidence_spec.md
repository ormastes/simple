# Hosted WM CSS override production evidence contract

> This source contract keeps the CSS fixture proof attached to the canonical

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted WM CSS override production evidence contract

This source contract keeps the CSS fixture proof attached to the canonical

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/wm_host_css_override_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This source contract keeps the CSS fixture proof attached to the canonical
hosted production launcher. It deliberately records its command channel as
synthetic diagnostic input, not Winit or physical interaction evidence.

## Scenarios

### Hosted WM CSS override evidence contract

#### uses a deterministic six-token fixture through the production launcher

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a deterministic six-token fixture through the production launcher
- Inspect the hosted CSS override evidence wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses a deterministic six-token fixture through the production launcher")
step("Inspect the hosted CSS override evidence wrapper")
val script = file_read("scripts/check/check-wm-host-css-override-evidence.shs")
expect(script).to_contain("check-wm-production-fullscreen-evidence.shs")
expect(script).to_contain("SIMPLE_WM_THEME_FILE=\"$theme_file\"")
expect(script).to_contain("--wm-bg: #10263d;")
expect(script).to_contain("--wm-fg: #f8fbff;")
expect(script).to_contain("--wm-accent: #74d5ff;")
expect(script).to_contain("--wm-surface: #1b3654;")
expect(script).to_contain("--wm-surface-hover: #285070;")
expect(script).to_contain("--wm-error: #ff6f91;")
```

</details>

#### requires installed override effective material identity and changed presented pixels

- requires installed override effective material identity and changed presented pixels
- Inspect the CSS override assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires installed override effective material identity and changed presented pixels")
step("Inspect the CSS override assertions")
val script = file_read("scripts/check/check-wm-host-css-override-evidence.shs")
expect(script).to_contain("installed=true")
expect(script).to_contain("effective-material-identity-unchanged")
expect(script).to_contain("package-source-identity-unexpectedly-changed")
expect(script).to_contain("expected-presented-buffer-pixels-unchanged")
expect(script).to_contain("wm_host_css_override_effective_material_sha256")
expect(script).to_contain("wm_host_css_override_presented_pixels_changed=true")
expect(script).to_contain("diagnostic-synthetic-compositor-command-channel-not-winit-or-physical")
expect(script.contains("physical input evidence")).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d54cfca84e776df86992ef7fa4b89a82cca4e82b1fcae8a6fa3c91e52735ac29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d54cfca84e776df86992ef7fa4b89a82cca4e82b1fcae8a6fa3c91e52735ac29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d54cfca84e776df86992ef7fa4b89a82cca4e82b1fcae8a6fa3c91e52735ac29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/check/wm_host_css_override_evidence_spec.spl
mirror: doc/06_spec/03_system/check/wm_host_css_override_evidence_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/wm_host_css_override_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/wm_host_css_override_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/wm_host_css_override_evidence_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a deterministic six-token fixture through the production launcher' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wm_host_css_override_evidence_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires installed override effective material identity and changed presented pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
