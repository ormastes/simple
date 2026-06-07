# Pe Coff Header Specification

> <details>

<!-- sdn-diagram:id=pe_coff_header_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pe_coff_header_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pe_coff_header_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pe_coff_header_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pe Coff Header Specification

## Scenarios

### PE/COFF header classifier

#### rejects too-small inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = parse_pe_header_summary([])
expect(summary.ok).to_equal(false)
expect(summary.error).to_equal("too-small")
```

</details>

#### rejects non-MZ inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = parse_pe_header_summary(_zero_bytes(256))
expect(summary.error).to_equal("bad-mz")
```

</details>

#### classifies a minimal PE32+ x86_64 console header

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = parse_pe_header_summary(_minimal_pe64_console())
expect(summary.ok).to_equal(true)
expect(summary.machine).to_equal("x86_64")
expect(summary.optional_header).to_equal("PE32+")
expect(summary.subsystem_kind).to_equal("console")
```

</details>

#### accepts a bounded section table

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_section_table_gate(_minimal_pe64_console())).to_equal("ready")
```

</details>

#### requires import, relocation, and TLS data directories

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_data_directory_gate(_minimal_pe64_console())).to_equal("missing-import-directory")
expect(pe_data_directory_gate(_minimal_pe64_console_with_dirs())).to_equal("ready")
```

</details>

#### maps RVAs through section table bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_rva_to_file_offset(_minimal_pe64_console_with_import_descriptor(), 0x2040)).to_equal(0x240)
expect(pe_rva_to_file_offset(_minimal_pe64_console_with_import_descriptor(), 0x9000)).to_equal(-1)
```

</details>

#### validates section raw/virtual bounds and entry execute permission

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_section_bounds_gate(_minimal_pe64_console_with_import_descriptor())).to_equal("ready")
expect(pe_entry_section_executable_gate(_minimal_pe64_console_with_import_descriptor())).to_equal("ready")
```

</details>

#### validates the first import descriptor name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_import_directory_gate(_minimal_pe64_console_with_dirs())).to_equal("import-directory-out-of-bounds")
expect(pe_import_directory_gate(_minimal_pe64_console_with_import_descriptor())).to_equal("ready")
```

</details>

#### requires a null import descriptor terminator after the first descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_import_directory_gate(_minimal_pe64_console_with_unterminated_import_descriptor())).to_equal("import-descriptor-unterminated")
```

</details>

#### validates a bounded import descriptor table without executing code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_import_descriptor_table_gate(_minimal_pe64_console_with_import_descriptor(), 4, 8)).to_equal("ready")
expect(pe_import_descriptor_table_gate(_minimal_pe64_console_with_two_import_descriptors(), 4, 8)).to_equal("ready")
expect(pe_import_descriptor_table_gate(_minimal_pe64_console_with_two_import_descriptors(), 1, 8)).to_equal("import-descriptor-limit-exceeded")
```

</details>

#### summarizes multiple import descriptors and thunk counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summaries = pe_import_descriptor_summaries(_minimal_pe64_console_with_two_import_descriptors(), 4, 8)
expect(summaries.len()).to_equal(2)
expect(summaries[0].dll_name).to_equal("KERNEL32.dll")
expect(summaries[0].descriptor_index).to_equal(0)
expect(summaries[0].lookup_thunk_rva).to_equal(0x2060)
expect(summaries[0].first_thunk_rva).to_equal(0x2070)
expect(summaries[0].symbol_count).to_equal(1)
expect(summaries[1].dll_name).to_equal("USER32.dll")
expect(summaries[1].descriptor_index).to_equal(1)
expect(summaries[1].lookup_thunk_rva).to_equal(0x20a0)
expect(summaries[1].first_thunk_rva).to_equal(0x20b0)
expect(summaries[1].symbol_count).to_equal(1)
```

</details>

#### extracts descriptor-qualified import thunk bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = pe_import_descriptor_thunk_bindings(_minimal_pe64_console_with_two_import_descriptors(), 4, 8)
expect(bindings.len()).to_equal(2)
expect(bindings[0].dll_name).to_equal("KERNEL32.dll")
expect(bindings[0].descriptor_index).to_equal(0)
expect(bindings[0].symbol).to_equal("WriteFile")
expect(bindings[0].thunk_index).to_equal(0)
expect(bindings[0].thunk_rva).to_equal(0x2060)
expect(bindings[0].iat_rva).to_equal(0x2070)
expect(bindings[0].name_rva).to_equal(0x2080)
expect(bindings[1].dll_name).to_equal("USER32.dll")
expect(bindings[1].descriptor_index).to_equal(1)
expect(bindings[1].symbol).to_equal("MessageBoxW")
expect(bindings[1].thunk_index).to_equal(0)
expect(bindings[1].thunk_rva).to_equal(0x20a0)
expect(bindings[1].iat_rva).to_equal(0x20b0)
expect(bindings[1].name_rva).to_equal(0x20c0)
```

</details>

#### validates relocation and TLS directories through mapped section bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_relocation_directory_gate(_minimal_pe64_console_with_dirs())).to_equal("relocation-directory-unmapped")
expect(pe_relocation_directory_gate(_minimal_pe64_console_with_import_descriptor())).to_equal("ready")
expect(pe_tls_directory_gate(_minimal_pe64_console_with_import_descriptor())).to_equal("ready")
```

</details>

#### extracts the first import DLL name without executing code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_first_import_dll_name(_minimal_pe64_console_with_dirs())).to_equal("")
expect(pe_first_import_dll_name(_minimal_pe64_console_with_import_descriptor())).to_equal("KERNEL32.dll")
```

</details>

#### extracts imported symbol names from the first thunk table

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = pe_first_import_symbol_names(_minimal_pe64_console_with_import_descriptor(), 8)
expect(symbols.len()).to_equal(1)
expect(symbols[0]).to_equal("WriteFile")
```

</details>

#### validates the first import thunk table before extracting symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pe_first_import_thunk_gate(_minimal_pe64_console_with_import_descriptor(), 8)).to_equal("ready")
expect(pe_first_import_thunk_gate(_minimal_pe64_console_with_import_descriptor(), 1)).to_equal("import-thunk-limit-exceeded")
expect(pe_first_import_thunk_gate(_minimal_pe64_console_with_bad_import_name_rva(), 8)).to_equal("import-symbol-name-unmapped")
```

</details>

#### extracts imported symbol name RVAs from the first thunk table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = pe_first_import_symbol_bindings(_minimal_pe64_console_with_import_descriptor(), 8)
expect(bindings.len()).to_equal(1)
expect(bindings[0].symbol).to_equal("WriteFile")
expect(bindings[0].name_rva).to_equal(0x2080)
```

</details>

#### extracts import lookup thunk RVAs separately from symbol name RVAs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = pe_first_import_thunk_bindings(_minimal_pe64_console_with_import_descriptor(), 8)
expect(bindings.len()).to_equal(1)
expect(bindings[0].symbol).to_equal("WriteFile")
expect(bindings[0].thunk_index).to_equal(0)
expect(bindings[0].thunk_rva).to_equal(0x2060)
expect(bindings[0].name_rva).to_equal(0x2080)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pe_coff_header_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PE/COFF header classifier

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
