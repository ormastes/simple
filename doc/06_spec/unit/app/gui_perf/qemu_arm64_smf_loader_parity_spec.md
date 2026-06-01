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
| Source | `test/unit/app/gui_perf/qemu_arm64_smf_loader_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that SimpleOS dynload evidence, not just an artifact contract, is
required before the pure GUI command batch can satisfy the QEMU ARM64 adapter
parity row.

## Examples

A passing row starts with `GUI_QEMU_ARM64_SMF_LOADER_PARITY
status=loader-contract-pass` and includes `loader=simpleos_smf_dynload`,
`adapter=simpleos-framebuffer-virtio`, `dynload_pass=true`, and `live_qemu=false`.

**Requirements:** N/A
**Plan:** doc/03_plan/gui_hardening_current_plan_2026-06-01.md
**Design:** doc/05_design/gui_color_image_pipeline_8k.md
**Research:** doc/01_research/local/gui_color_image_pipeline_8k.md

## Scenarios

### QEMU ARM64 SMF loader parity

#### accepts SimpleOS dynloaded SMF artifacts reaching the pure GUI adapter

1. Pair passing SimpleOS dynload evidence with a representative GUI command batch
   - Expected: parity.status equals `loader-contract-pass`
   - Expected: parity.loader equals `simpleos_smf_dynload`
   - Expected: parity.dynload_pass is true

2. Emit the loader-backed QEMU parity evidence row


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parity = gui_qemu_arm64_smf_loader_parity(_good_dynload_evidence(), _representative_batch())
expect(parity.status).to_equal("loader-contract-pass")
expect(parity.loader).to_equal("simpleos_smf_dynload")
expect(parity.dynload_pass).to_equal(true)
val row = gui_qemu_arm64_smf_loader_parity_row(parity)
expect(row).to_contain("GUI_QEMU_ARM64_SMF_LOADER_PARITY")
expect(row).to_contain("status=loader-contract-pass")
expect(row).to_contain("adapter=simpleos-framebuffer-virtio")
expect(row).to_contain("live_qemu=false")
```

</details>

#### fails closed without SimpleOS dynload success

1. Mark the dynload probe as failed even though the artifact metadata looks correct
   - Expected: parity.status equals `loader-contract-fail`
   - Expected: parity.dynload_pass is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parity = gui_qemu_arm64_smf_loader_parity(_failed_dynload_evidence(), _representative_batch())
expect(parity.status).to_equal("loader-contract-fail")
expect(parity.dynload_pass).to_equal(false)
```

</details>

#### fails closed for empty command batches

1. Keep dynload evidence valid but remove the GUI command batch
   - Expected: parity.status equals `loader-contract-fail`
   - Expected: parity.reason equals `missing-simpleos-dynload-or-command-batch`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parity = gui_qemu_arm64_smf_loader_parity(_good_dynload_evidence(), gui_empty_batch())
expect(parity.status).to_equal("loader-contract-fail")
expect(parity.reason).to_equal("missing-simpleos-dynload-or-command-batch")
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

- **Plan:** [doc/03_plan/gui_hardening_current_plan_2026-06-01.md](doc/03_plan/gui_hardening_current_plan_2026-06-01.md)
- **Design:** [doc/05_design/gui_color_image_pipeline_8k.md](doc/05_design/gui_color_image_pipeline_8k.md)
- **Research:** [doc/01_research/local/gui_color_image_pipeline_8k.md](doc/01_research/local/gui_color_image_pipeline_8k.md)

