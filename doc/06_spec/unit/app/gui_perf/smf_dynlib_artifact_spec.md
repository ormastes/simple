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

#### wraps and extracts a role-2 SMF dynlib through runtime file SFFI

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dynlib_path = "/tmp/simple_gui_smf_dynlib_fixture.so"
val smf_path = "/tmp/simple_gui_smf_dynlib_fixture.smf"
val extracted_path = "/tmp/simple_gui_smf_dynlib_fixture.extracted.so"
expect(rt_file_write_bytes(dynlib_path, [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8])).to_equal(true)
expect(rt_file_wrap_smf_dynlib(dynlib_path, smf_path, 1)).to_equal(true)
expect(rt_file_extract_smf_dynlib(smf_path, extracted_path)).to_equal(true)
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
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

