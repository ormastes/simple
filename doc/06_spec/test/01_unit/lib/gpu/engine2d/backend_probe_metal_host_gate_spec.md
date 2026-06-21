# Metal Strict Backend Host Gate Specification

> Verifies that strict Engine2D Metal backend selection reports the canonical macOS host gate instead of generic runtime-evidence text or CPU fallback.

<!-- sdn-diagram:id=backend_probe_metal_host_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_probe_metal_host_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_probe_metal_host_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_probe_metal_host_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Strict Backend Host Gate Specification

Verifies that strict Engine2D Metal backend selection reports the canonical macOS host gate instead of generic runtime-evidence text or CPU fallback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/ui/misc/production_gui_web_renderer_parity_hardening.md |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md |
| Research | doc/09_report/metal_generated_2d_readback_2026-06-16.md |
| Source | `test/01_unit/lib/gpu/engine2d/backend_probe_metal_host_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that strict Engine2D Metal backend selection reports the canonical
macOS host gate instead of generic runtime-evidence text or CPU fallback.

**Requirements:** doc/02_requirements/ui/misc/production_gui_web_renderer_parity_hardening.md
**Research:** doc/09_report/metal_generated_2d_readback_2026-06-16.md
**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Architecture:** doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md
**Design:** doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md
**Report:** doc/09_report/metal_generated_2d_readback_2026-06-16.md

## Syntax

Use `StrictBackendFactory.strict().create_backend("metal")` when callers need
typed diagnostics for unavailable Metal evidence.

## Scenarios

### Metal strict backend host gate

#### reports macOS host requirement without CPU fallback

- Request strict Metal backend selection
- Confirm strict selection stayed on Metal
   - Expected: probe.requested_name equals `metal`
   - Expected: probe.selected_name equals `metal`
   - Expected: probe.backend_name equals `metal`
   - Expected: probe.api_name equals `metal`
   - Expected: probe.shader_format equals `msl`
- Confirm Metal reports the canonical macOS host gate
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: probe.feature_gate equals `macos`
   - Expected: probe.reason equals `metal-requires-macos`
   - Expected: probe.fallback_reason equals `metal-requires-macos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request strict Metal backend selection")
val probe = StrictBackendFactory.strict().create_backend("metal")

step("Confirm strict selection stayed on Metal")
expect(probe.requested_name).to_equal("metal")
expect(probe.selected_name).to_equal("metal")
expect(probe.backend_name).to_equal("metal")
expect(probe.api_name).to_equal("metal")
expect(probe.shader_format).to_equal("msl")

step("Confirm Metal reports the canonical macOS host gate")
expect(probe.status).to_equal(BackendStatus.Unavailable)
expect(probe.feature_gate).to_equal("macos")
expect(probe.reason).to_equal("metal-requires-macos")
expect(probe.fallback_reason).to_equal("metal-requires-macos")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/ui/misc/production_gui_web_renderer_parity_hardening.md](doc/02_requirements/ui/misc/production_gui_web_renderer_parity_hardening.md)
- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md](doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md)
- **Research:** [doc/09_report/metal_generated_2d_readback_2026-06-16.md](doc/09_report/metal_generated_2d_readback_2026-06-16.md)


</details>
