# SimpleOS SMF dynload evidence

> Verifies that the pure GUI SMF artifact can pass through the SimpleOS dynload registry and resolve the hot-call symbol.

<!-- sdn-diagram:id=simpleos_smf_dynload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_smf_dynload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_smf_dynload_spec -> std
simpleos_smf_dynload_spec -> app
simpleos_smf_dynload_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_smf_dynload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS SMF dynload evidence

Verifies that the pure GUI SMF artifact can pass through the SimpleOS dynload registry and resolve the hot-call symbol.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/gui_hardening_current_plan_2026-06-01.md |
| Design | doc/05_design/gui_color_image_pipeline_8k.md |
| Research | doc/01_research/local/gui_color_image_pipeline_8k.md |
| Source | `test/01_unit/app/gui_perf/simpleos_smf_dynload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the pure GUI SMF artifact can pass through the SimpleOS dynload
registry and resolve the hot-call symbol.

This is contract evidence for the GUI hardening release lane. It does not claim
live QEMU execution or pixel rendering. It proves that a role-2 ARM64 SMF
library envelope containing the GUI hot-call symbol can be opened through the
SimpleOS loader registry, resolved through `loader_dynsym`, and reported as a
machine-readable `GUI_SIMPLEOS_SMF_DYNLOAD` row. It also proves that wrong
symbols, wrong architectures, and missing artifact bytes fail closed.

## Examples

The expected passing row starts with `GUI_SIMPLEOS_SMF_DYNLOAD
status=simpleos-dynload-pass` and includes
`symbol=gui_dynlib_hot_probe_tick`, `loader=smf_dynlib`,
`adapter=simpleos-framebuffer-virtio`, and `pass=true`.

**Requirements:** N/A
**Plan:** doc/03_plan/gui_hardening_current_plan_2026-06-01.md
**Design:** doc/05_design/gui_color_image_pipeline_8k.md
**Research:** doc/01_research/local/gui_color_image_pipeline_8k.md

## Scenarios

### SimpleOS SMF dynload evidence

#### opens an ARM64 role-2 SMF and resolves the GUI hot-call symbol

1. Reset the dynlib registry before probing the artifact
2. Build a role-2 ARM64 SMF envelope with the GUI hot-call symbol
3. Probe the SMF envelope through the SimpleOS dynload registry
   - Expected: evidence.pass is true
   - Expected: evidence.loader equals `smf_dynlib`
   - Expected: evidence.symbol_addr equals `0x400010`
   - Expected: evidence.process_callable is true
4. Emit a machine-readable SimpleOS dynload evidence row


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val smf = gui_smf_wrap_native_library(_elf64_with_gui_hot_dynsym(), 3u8)
val evidence = gui_simpleos_smf_dynload_probe("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
expect(evidence.pass).to_equal(true)
expect(evidence.loader).to_equal("smf_dynlib")
expect(evidence.symbol_addr).to_equal(0x400010)
expect(evidence.process_callable).to_equal(true)
val row = gui_simpleos_smf_dynload_row(evidence)
expect(row).to_contain("GUI_SIMPLEOS_SMF_DYNLOAD")
expect(row).to_contain("status=simpleos-dynload-pass")
expect(row).to_contain("symbol=gui_dynlib_hot_probe_tick")
expect(row).to_contain("process_callable=true")
expect(row).to_contain("pass=true")
```

</details>

#### fails closed for a wrong symbol

1. Build a valid ARM64 SMF envelope
2. Probe a symbol that is not the GUI release hot-call symbol
   - Expected: evidence.pass is false
   - Expected: evidence.error equals `wrong-symbol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val smf = gui_smf_wrap_native_library(_elf64_with_gui_hot_dynsym(), 3u8)
val evidence = gui_simpleos_smf_dynload_probe("build/gui/pure_gui_hot.smf", smf, "other_symbol")
expect(evidence.pass).to_equal(false)
expect(evidence.error).to_equal("wrong-symbol")
```

</details>

#### fails closed for non-ARM64 SMF library envelopes

1. Build a role-2 SMF envelope for the wrong architecture
2. Probe the wrong-architecture artifact through the ARM64 dynload path
   - Expected: evidence.pass is false
   - Expected: evidence.error equals `not-arm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val smf = gui_smf_wrap_native_library(_elf64_with_gui_hot_dynsym(), 1u8)
val evidence = gui_simpleos_smf_dynload_probe("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
expect(evidence.pass).to_equal(false)
expect(evidence.error).to_equal("not-arm64")
expect(evidence.handle).to_be_less_than(0)
```

</details>

#### fails closed for missing artifact bytes

1. Probe an empty artifact without registering a dynload handle
   - Expected: evidence.pass is false
   - Expected: evidence.error equals `bad-smf-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val evidence = gui_simpleos_smf_dynload_probe("", [], "gui_dynlib_hot_probe_tick")
expect(evidence.pass).to_equal(false)
expect(evidence.error).to_equal("bad-smf-contract")
expect(evidence.handle).to_be_less_than(0)
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

- **Plan:** [doc/03_plan/gui_hardening_current_plan_2026-06-01.md](doc/03_plan/gui_hardening_current_plan_2026-06-01.md)
- **Design:** [doc/05_design/gui_color_image_pipeline_8k.md](doc/05_design/gui_color_image_pipeline_8k.md)
- **Research:** [doc/01_research/local/gui_color_image_pipeline_8k.md](doc/01_research/local/gui_color_image_pipeline_8k.md)


</details>
