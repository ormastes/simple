# QEMU ARM64 SMF loader parity

> Verifies that SimpleOS dynload evidence, not just an artifact contract, is required before the pure GUI command batch can satisfy the QEMU ARM64 adapter parity row.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU ARM64 SMF loader parity

Verifies that SimpleOS dynload evidence, not just an artifact contract, is required before the pure GUI command batch can satisfy the QEMU ARM64 adapter parity row.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/gui_hardening_current_plan_2026-06-01.md |
| Design | doc/05_design/gui_color_image_pipeline_8k.md |
| Research | doc/01_research/local/gui_color_image_pipeline_8k.md |
| Source | `test/01_unit/app/gui_perf/qemu_arm64_smf_loader_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that SimpleOS dynload evidence, not just an artifact contract, is
required before the pure GUI command batch can satisfy the QEMU ARM64 adapter
parity row.

## Examples

A passing row starts with `GUI_QEMU_ARM64_SMF_LOADER_PARITY
status=loader-contract-pass` and includes `loader=smf_dynlib`,
`adapter=simpleos-framebuffer-virtio`, `dynload_pass=true`, and `live_qemu=false`.

**Requirements:** N/A
**Plan:** doc/03_plan/gui_hardening_current_plan_2026-06-01.md
**Design:** doc/05_design/gui_color_image_pipeline_8k.md
**Research:** doc/01_research/local/gui_color_image_pipeline_8k.md

## Scenarios

### QEMU ARM64 SMF loader parity

#### accepts SimpleOS dynloaded SMF artifacts reaching the pure GUI adapter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts SimpleOS dynloaded SMF artifacts reaching the pure GUI adapter
- Pair passing SimpleOS dynload evidence with a representative GUI command batch
   - Expected: parity.status equals `loader-contract-pass`
   - Expected: parity.loader equals `smf_dynlib`
   - Expected: parity.dynload_pass is true
- Emit the loader-backed QEMU parity evidence row


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts SimpleOS dynloaded SMF artifacts reaching the pure GUI adapter")
val parity = gui_qemu_arm64_smf_loader_parity(_good_dynload_evidence(), _representative_batch())
expect(parity.status).to_equal("loader-contract-pass")
expect(parity.loader).to_equal("smf_dynlib")
expect(parity.dynload_pass).to_equal(true)
val row = gui_qemu_arm64_smf_loader_parity_row(parity)
expect(row).to_contain("GUI_QEMU_ARM64_SMF_LOADER_PARITY")
expect(row).to_contain("status=loader-contract-pass")
expect(row).to_contain("adapter=simpleos-framebuffer-virtio")
expect(row).to_contain("live_qemu=false")
```

</details>

#### fails closed without SimpleOS dynload success

- fails closed without SimpleOS dynload success
- Mark the dynload probe as failed even though the artifact metadata looks correct
   - Expected: parity.status equals `loader-contract-fail`
   - Expected: parity.dynload_pass is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed without SimpleOS dynload success")
val parity = gui_qemu_arm64_smf_loader_parity(_failed_dynload_evidence(), _representative_batch())
expect(parity.status).to_equal("loader-contract-fail")
expect(parity.dynload_pass).to_equal(false)
```

</details>

#### fails closed for forged dynload pass flags

- fails closed for forged dynload pass flags
- Keep pass=true but remove the SimpleOS dynload status identity
   - Expected: gui_qemu_arm64_smf_loader_parity(wrong_status, _representative_batch()).status equals `loader-contract-fail`
- Keep pass=true but point the evidence at a non-SimpleOS adapter
   - Expected: gui_qemu_arm64_smf_loader_parity(wrong_adapter, _representative_batch()).status equals `loader-contract-fail`
- Keep pass=true but remove the process-callable mapped symbol proof
   - Expected: gui_qemu_arm64_smf_loader_parity(not_callable, _representative_batch()).status equals `loader-contract-fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for forged dynload pass flags")
val wrong_status = GuiSimpleOsSmfDynloadEvidence(
    status: "simpleos-dynload-fail",
    artifact_path: "build/gui/pure_gui_hot.smf",
    smf_role: 2,
    arch_code: 3,
    embedded_dynlib: true,
    symbol_name: "gui_dynlib_hot_probe_tick",
    loader: "smf_dynlib",
    adapter: "simpleos-framebuffer-virtio",
    handle: 1,
    symbol_addr: 0x400010,
    process_callable: true,
    pass: true,
    error: ""
)
expect(gui_qemu_arm64_smf_loader_parity(wrong_status, _representative_batch()).status).to_equal("loader-contract-fail")
val wrong_adapter = GuiSimpleOsSmfDynloadEvidence(
    status: "simpleos-dynload-pass",
    artifact_path: "build/gui/pure_gui_hot.smf",
    smf_role: 2,
    arch_code: 3,
    embedded_dynlib: true,
    symbol_name: "gui_dynlib_hot_probe_tick",
    loader: "smf_dynlib",
    adapter: "host-dynlib",
    handle: 1,
    symbol_addr: 0x400010,
    process_callable: true,
    pass: true,
    error: ""
)
expect(gui_qemu_arm64_smf_loader_parity(wrong_adapter, _representative_batch()).status).to_equal("loader-contract-fail")
val not_callable = GuiSimpleOsSmfDynloadEvidence(
    status: "simpleos-dynload-pass",
    artifact_path: "build/gui/pure_gui_hot.smf",
    smf_role: 2,
    arch_code: 3,
    embedded_dynlib: true,
    symbol_name: "gui_dynlib_hot_probe_tick",
    loader: "smf_dynlib",
    adapter: "simpleos-framebuffer-virtio",
    handle: 1,
    symbol_addr: 0x400010,
    process_callable: false,
    pass: true,
    error: ""
)
expect(gui_qemu_arm64_smf_loader_parity(not_callable, _representative_batch()).status).to_equal("loader-contract-fail")
```

</details>

#### fails closed for empty command batches

- fails closed for empty command batches
- Keep dynload evidence valid but remove the GUI command batch
   - Expected: parity.status equals `loader-contract-fail`
   - Expected: parity.reason equals `missing-smf-dynlib-or-command-batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for empty command batches")
val parity = gui_qemu_arm64_smf_loader_parity(_good_dynload_evidence(), gui_empty_batch())
expect(parity.status).to_equal("loader-contract-fail")
expect(parity.reason).to_equal("missing-smf-dynlib-or-command-batch")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/gui_hardening_current_plan_2026-06-01.md`
- **Design:** `doc/05_design/gui_color_image_pipeline_8k.md`
- **Research:** `doc/01_research/local/gui_color_image_pipeline_8k.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `902a5377d69fa715fe25aab71a22909f4cfac0d9b6448c0768145aa06cc7ab56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `902a5377d69fa715fe25aab71a22909f4cfac0d9b6448c0768145aa06cc7ab56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `902a5377d69fa715fe25aab71a22909f4cfac0d9b6448c0768145aa06cc7ab56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/app/gui_perf/qemu_arm64_smf_loader_parity_spec.spl
mirror: doc/06_spec/01_unit/app/gui_perf/qemu_arm64_smf_loader_parity_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/gui_perf/qemu_arm64_smf_loader_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/gui_perf/qemu_arm64_smf_loader_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
