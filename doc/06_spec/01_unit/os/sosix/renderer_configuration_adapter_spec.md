# Renderer Configuration Adapter Specification

> Tests covering SOSIX renderer configuration capability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Renderer Configuration Adapter Specification

## Scenarios

### SOSIX renderer configuration capability

#### defaults an empty capability selection to software without ambient host access

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults an empty capability selection to software without ambient host access
   - Expected: host_wm_render_backend_key_from_configuration(configuration) equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults an empty capability selection to software without ambient host access")
val configuration = sosix_host_configuration_snapshot_create(
    "headless", "queue", "", false, "")
expect(host_wm_render_backend_key_from_configuration(configuration)).to_equal("software")
```

</details>

#### normalizes and applies an explicit backend selection

- normalizes and applies an explicit backend selection
   - Expected: host_wm_render_backend_key_from_configuration(configuration) equals `software`
   - Expected: raster.selected_backend() equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes and applies an explicit backend selection")
val configuration = sosix_host_configuration_snapshot_create(
    "hosted", "queue", "  software  ", false, "")
expect(host_wm_render_backend_key_from_configuration(configuration)).to_equal("software")
var raster = Engine2dCompositorBackend.create_from_host_configuration(
    2, 2, configuration)
expect(raster.selected_backend()).to_equal("software")
raster.shutdown()
```

</details>

#### captures transfer settings in one immutable snapshot profile

- captures transfer settings in one immutable snapshot profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures transfer settings in one immutable snapshot profile")
val configuration =
    sosix_host_configuration_snapshot_create_with_engine2d_transfer(
        "hosted", "queue", "software", false, "",
        "upload", "bulk", "mapped", "readback")
expect(engine2d_compositor_transfer_profile_from_configuration(
    configuration)).to_equal("upload\0bulk\0mapped\0readback")
```

</details>

#### captures hosted environment settings once through the SOSIX adapter

- captures hosted environment settings once through the SOSIX adapter
   - Expected: configuration.display_backend equals `hosted`
   - Expected: configuration.input_backend equals `host-event-queue`
   - Expected: configuration.gpu_backend equals `software`
   - Expected: configuration.evidence_enabled is false
   - Expected: configuration.storage_root equals ``
   - Expected: raster.selected_backend() equals `software`
   - Expected: raster.host_transfer_profile equals `captured`
   - Expected: configuration.engine2d_transfer_path equals `mapped`
   - Expected: raster.host_transfer_profile equals `captured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures hosted environment settings once through the SOSIX adapter")
env_set("SIMPLE_GUI_BACKEND", "software")
env_set("SIMPLE_ONE_CALL_UPLOAD", "1")
env_set("SIMPLE_BULK_UPLOAD", "0")
env_set("SIMPLE_SPL_GPU_TRANSFER_PATH", "mapped")
env_set("SIMPLE_ONE_CALL_READBACK", "1")
val configuration = sosix_host_configuration_from_environment()
val captured = "1\0" + "0\0" + "mapped\0" + "1"
expect(configuration.display_backend).to_equal("hosted")
expect(configuration.input_backend).to_equal("host-event-queue")
expect(configuration.gpu_backend).to_equal("software")
expect(configuration.evidence_enabled).to_equal(false)
expect(configuration.storage_root).to_equal("")
expect(engine2d_compositor_transfer_profile_from_configuration(
    configuration)).to_equal(captured)
var raster = Engine2dCompositorBackend.create_from_host_configuration(
    2, 2, configuration)
expect(raster.selected_backend()).to_equal("software")
expect(raster.host_transfer_profile).to_equal(captured)
env_set("SIMPLE_SPL_GPU_TRANSFER_PATH", "changed-after-create")
expect(configuration.engine2d_transfer_path).to_equal("mapped")
expect(raster.host_transfer_profile).to_equal(captured)
raster.shutdown()
env_unset("SIMPLE_GUI_BACKEND")
env_unset("SIMPLE_ONE_CALL_UPLOAD")
env_unset("SIMPLE_BULK_UPLOAD")
env_unset("SIMPLE_SPL_GPU_TRANSFER_PATH")
env_unset("SIMPLE_ONE_CALL_READBACK")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/renderer_configuration_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SOSIX renderer configuration capability.
- SOSIX renderer configuration capability

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

- Canonical SPipe generation for source `fe14135f79841464d105b904bd05bd5d988c21e6f68167061c1f31e84ce8d18b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe14135f79841464d105b904bd05bd5d988c21e6f68167061c1f31e84ce8d18b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe14135f79841464d105b904bd05bd5d988c21e6f68167061c1f31e84ce8d18b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/sosix/renderer_configuration_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/renderer_configuration_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/renderer_configuration_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/renderer_configuration_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/renderer_configuration_adapter_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults an empty capability selection to software without ambient host access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/renderer_configuration_adapter_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes and applies an explicit backend selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/renderer_configuration_adapter_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures transfer settings in one immutable snapshot profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
