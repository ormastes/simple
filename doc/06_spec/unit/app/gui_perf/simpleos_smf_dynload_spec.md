# SimpleOS SMF dynload evidence

Verifies that the pure GUI SMF artifact can pass through the SimpleOS dynload

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/gui_perf/simpleos_smf_dynload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that the pure GUI SMF artifact can pass through the SimpleOS dynload
registry and resolve the hot-call symbol.

## Scenarios

### SimpleOS SMF dynload evidence

#### opens an ARM64 role-2 SMF and resolves the GUI hot-call symbol

1. Reset the dynlib registry before probing the artifact

2. Build a role-2 ARM64 SMF envelope with the GUI hot-call symbol

3. Probe the SMF envelope through the SimpleOS dynload registry
   - Expected: evidence.pass is true
   - Expected: evidence.loader equals `simpleos_smf_dynload`
   - Expected: evidence.symbol_addr equals `0x400010`

4. Emit a machine-readable SimpleOS dynload evidence row


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val smf = gui_smf_wrap_native_library(_elf64_with_gui_hot_dynsym(), 3u8)
val evidence = gui_simpleos_smf_dynload_probe("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
expect(evidence.pass).to_equal(true)
expect(evidence.loader).to_equal("simpleos_smf_dynload")
expect(evidence.symbol_addr).to_equal(0x400010)
val row = gui_simpleos_smf_dynload_row(evidence)
expect(row).to_contain("GUI_SIMPLEOS_SMF_DYNLOAD")
expect(row).to_contain("status=simpleos-dynload-pass")
expect(row).to_contain("symbol=gui_dynlib_hot_probe_tick")
expect(row).to_contain("pass=true")
```

</details>

#### fails closed for a wrong symbol

1. Build a valid ARM64 SMF envelope

2. Probe a symbol that is not the GUI release hot-call symbol
   - Expected: evidence.pass is false
   - Expected: evidence.error equals `wrong-symbol`


<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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

