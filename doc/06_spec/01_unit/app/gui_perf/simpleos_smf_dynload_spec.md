# SimpleOS SMF dynload evidence

> Verifies that the pure GUI SMF artifact can pass through the SimpleOS dynload registry and resolve the hot-call symbol.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens an ARM64 role-2 SMF and resolves the GUI hot-call symbol
- Reset the dynlib registry before probing the artifact
- Build a role-2 ARM64 SMF envelope with the GUI hot-call symbol
- Probe the SMF envelope through the SimpleOS dynload registry
   - Expected: evidence.pass is true
   - Expected: evidence.loader equals `smf_dynlib`
   - Expected: evidence.symbol_addr equals `0x400010`
   - Expected: evidence.process_callable is true
- Emit a machine-readable SimpleOS dynload evidence row


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("opens an ARM64 role-2 SMF and resolves the GUI hot-call symbol")
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

- fails closed for a wrong symbol
- Build a valid ARM64 SMF envelope
- Probe a symbol that is not the GUI release hot-call symbol
   - Expected: evidence.pass is false
   - Expected: evidence.error equals `wrong-symbol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for a wrong symbol")
dylib_registry_reset_for_test()
val smf = gui_smf_wrap_native_library(_elf64_with_gui_hot_dynsym(), 3u8)
val evidence = gui_simpleos_smf_dynload_probe("build/gui/pure_gui_hot.smf", smf, "other_symbol")
expect(evidence.pass).to_equal(false)
expect(evidence.error).to_equal("wrong-symbol")
```

</details>

#### fails closed for non-ARM64 SMF library envelopes

- fails closed for non-ARM64 SMF library envelopes
- Build a role-2 SMF envelope for the wrong architecture
- Probe the wrong-architecture artifact through the ARM64 dynload path
   - Expected: evidence.pass is false
   - Expected: evidence.error equals `not-arm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for non-ARM64 SMF library envelopes")
dylib_registry_reset_for_test()
val smf = gui_smf_wrap_native_library(_elf64_with_gui_hot_dynsym(), 1u8)
val evidence = gui_simpleos_smf_dynload_probe("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
expect(evidence.pass).to_equal(false)
expect(evidence.error).to_equal("not-arm64")
expect(evidence.handle).to_be_less_than(0)
```

</details>

#### fails closed for missing artifact bytes

- fails closed for missing artifact bytes
- Probe an empty artifact without registering a dynload handle
   - Expected: evidence.pass is false
   - Expected: evidence.error equals `bad-smf-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for missing artifact bytes")
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

- Canonical SPipe generation for source `7ffccbf9ae7f59f7b43b4932b6e5f83af1e66a9d749ffd00a1af10f1d227ce65`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ffccbf9ae7f59f7b43b4932b6e5f83af1e66a9d749ffd00a1af10f1d227ce65`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ffccbf9ae7f59f7b43b4932b6e5f83af1e66a9d749ffd00a1af10f1d227ce65`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/gui_perf/simpleos_smf_dynload_spec.spl
mirror: doc/06_spec/01_unit/app/gui_perf/simpleos_smf_dynload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/gui_perf/simpleos_smf_dynload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/gui_perf/simpleos_smf_dynload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/gui_perf/simpleos_smf_dynload_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens an ARM64 role-2 SMF and resolves the GUI hot-call symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/gui_perf/simpleos_smf_dynload_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for a wrong symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/gui_perf/simpleos_smf_dynload_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for non-ARM64 SMF library envelopes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
