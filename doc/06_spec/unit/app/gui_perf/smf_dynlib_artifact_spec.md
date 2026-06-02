# Smf Dynlib Artifact Specification

## Scenarios

### pure GUI SMF dynlib artifact

#### maps common host architecture names to SMF arch codes

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_smf_dynlib_arch_code("x86_64")).to_equal(1u8)
expect(gui_smf_dynlib_arch_code("amd64")).to_equal(1u8)
expect(gui_smf_dynlib_arch_code("arm64")).to_equal(3u8)
expect(gui_smf_dynlib_arch_code("aarch64")).to_equal(3u8)
expect(gui_smf_dynlib_arch_code("weird")).to_equal(0u8)
```

</details>

#### wraps an ELF host dynlib as a role-2 SMF library envelope

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8], 1u8)
expect(smf.len()).to_equal(6 + (SMF_HEADER_TRAILER_SIZE as i32))
val header = smf_parse_header(smf)
expect(header == nil).to_equal(false)
val parsed = header.unwrap()
expect(parsed.stub_size).to_equal(6i64)
expect(parsed.smf_data_offset).to_equal(6i64)
expect(parsed.role).to_equal(2i64)
expect(parsed.arch).to_equal(1i64)
val stub = smf_extract_library_stub_for_arch(smf, Architecture.X86_64)
expect(stub.is_ok()).to_equal(true)
expect(stub.unwrap().len()).to_equal(6)
```

</details>

#### wraps a Mach-O host dynlib as a role-2 arm64 SMF library envelope

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 0u8], 3u8)
val stub = smf_extract_library_stub_for_arch(smf, Architecture.Arm64)
expect(stub.is_ok()).to_equal(true)
expect(stub.unwrap()[0]).to_equal(0xCFu8)
```

</details>

#### emits a contract-only row without claiming QEMU or macOS execution

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 0u8], 3u8)
val contract = gui_smf_artifact_contract("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
expect(contract.status).to_equal("pass")
expect(contract.smf_role).to_equal(2i64)
expect(contract.arch_code).to_equal(3i64)
expect(contract.embedded_dynlib).to_equal(true)
expect(contract.qemu_status).to_equal("not-run")
expect(contract.macos_status).to_equal("not-run")
val row = gui_smf_artifact_contract_row(contract)
expect(row).to_start_with("GUI_SMF_ARTIFACT_CONTRACT status=pass")
expect(row).to_contain(" qemu_status=not-run ")
expect(row).to_contain(" qemu_reason=live-qemu-not-executed ")
expect(row).to_contain(" macos_status=not-run ")
expect(row).to_contain(" macos_reason=requires-macos-arm64")
```

</details>

#### fails closed for an embedded dynlib with a non-arm64 release arch

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8], 1u8)
val contract = gui_smf_artifact_contract("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
expect(contract.status).to_equal("fail")
expect(contract.smf_role).to_equal(2i64)
expect(contract.arch_code).to_equal(1i64)
expect(contract.embedded_dynlib).to_equal(true)
val row = gui_smf_artifact_contract_row(contract)
expect(row).to_start_with("GUI_SMF_ARTIFACT_CONTRACT status=fail")
expect(row).to_contain(" arch=1 ")
expect(row).to_contain(" symbol=gui_dynlib_hot_probe_tick ")
```

</details>

#### fails closed for an embedded arm64 dynlib with the wrong release symbol

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 0u8], 3u8)
val contract = gui_smf_artifact_contract("build/gui/pure_gui_hot.smf", smf, "unexpected_probe")
expect(contract.status).to_equal("fail")
expect(contract.smf_role).to_equal(2i64)
expect(contract.arch_code).to_equal(3i64)
expect(contract.embedded_dynlib).to_equal(true)
val row = gui_smf_artifact_contract_row(contract)
expect(row).to_start_with("GUI_SMF_ARTIFACT_CONTRACT status=fail")
expect(row).to_contain(" arch=3 ")
expect(row).to_contain(" symbol=unexpected_probe ")
```

</details>

#### fails closed for non-SMF artifact bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = gui_smf_artifact_contract("build/gui/not_a_dynlib.smf", [1u8, 2u8, 3u8, 4u8], "gui_dynlib_hot_probe_tick")
expect(contract.status).to_equal("fail")
expect(contract.smf_role).to_equal(-1i64)
expect(contract.embedded_dynlib).to_equal(false)
expect(contract.qemu_status).to_equal("not-run")
expect(contract.qemu_reason).to_equal("live-qemu-not-executed")
expect(contract.macos_status).to_equal("not-run")
expect(contract.macos_reason).to_equal("requires-macos-arm64")
```

</details>

#### fails closed for an empty SMF library envelope

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([], 1u8)
val contract = gui_smf_artifact_contract("build/gui/empty_dynlib.smf", smf, "gui_dynlib_hot_probe_tick")
expect(contract.status).to_equal("fail")
expect(contract.embedded_dynlib).to_equal(false)
expect(contract.qemu_status).to_equal("not-run")
expect(contract.qemu_reason).to_equal("live-qemu-not-executed")
expect(contract.macos_status).to_equal("not-run")
expect(contract.macos_reason).to_equal("requires-macos-arm64")
```

</details>

#### emits a missing artifact contract row

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = gui_smf_artifact_contract_row(gui_smf_artifact_contract_missing("", "gui_dynlib_hot_probe_tick"))
expect(row).to_start_with("GUI_SMF_ARTIFACT_CONTRACT status=missing")
expect(row).to_contain(" qemu_reason=live-qemu-not-executed ")
expect(row).to_contain(" macos_reason=requires-macos-arm64")
```

</details>

#### wraps and extracts a role-2 SMF dynlib through pure Simple helpers and file IO

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dynlib_path = "/tmp/simple_gui_smf_dynlib_fixture.so"
val smf_path = "/tmp/simple_gui_smf_dynlib_fixture.smf"
val extracted_path = "/tmp/simple_gui_smf_dynlib_fixture.extracted.so"
val dynlib_bytes = [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8]
expect(rt_file_write_bytes(dynlib_path, dynlib_bytes)).to_equal(true)
val loaded = rt_file_read_bytes(dynlib_path) ?? []
val smf = gui_smf_wrap_native_library(loaded, 1u8)
expect(rt_file_write_bytes(smf_path, smf)).to_equal(true)
val smf_loaded = rt_file_read_bytes(smf_path) ?? []
val stub = smf_extract_library_stub_for_arch(smf_loaded, Architecture.X86_64)
expect(stub.is_ok()).to_equal(true)
expect(rt_file_write_bytes(extracted_path, stub.unwrap())).to_equal(true)
val extracted = rt_file_read_bytes(extracted_path) ?? []
expect(extracted.len()).to_equal(6)
expect(extracted[0]).to_equal(0x7Fu8)
expect(extracted[1]).to_equal(0x45u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/gui_perf/smf_dynlib_artifact_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pure GUI SMF dynlib artifact

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

