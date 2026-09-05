# SMF parser

Verifies magic check + header parse of the minimal SMF loader.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/smf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies magic check + header parse of the minimal SMF loader.

## Scenarios

### smf_check_magic
_Magic validation._

#### rejects an empty buffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smf_check_magic(_empty())).to_equal(false)
```

</details>

#### accepts a buffer starting with the SMF magic bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smf_check_magic(_good_magic())).to_equal(true)
```

</details>

#### does not treat trailer-only SMF as offset-zero magic

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smf_check_magic(_trailer_magic())).to_equal(false)
```

</details>

### smf_has_header
_Header location detection._

#### accepts a v1.1 trailer header

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smf_has_header(_trailer_magic())).to_equal(true)
expect(smf_header_offset(_trailer_magic())).to_equal(5)
```

</details>

### smf_parse_header
_Header parsing either yields a descriptor or nil._

#### returns nil on an empty buffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = smf_parse_header(_empty())
expect(h.is_nil()).to_equal(true)
```

</details>

#### parses v1.1 trailer header fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = smf_parse_header(_trailer_magic())
expect(h == nil).to_equal(false)
val parsed = h.unwrap()
expect(parsed.header_offset).to_equal(5i64)
expect(parsed.entry_point).to_equal(52i64)
expect(parsed.stub_size).to_equal(5i64)
expect(parsed.smf_data_offset).to_equal(5i64)
```

</details>

#### magic constants spell 'SMF\\0'

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SMF64_MAGIC_0).to_equal(83u8)
expect(SMF64_MAGIC_1).to_equal(77u8)
expect(SMF64_MAGIC_2).to_equal(70u8)
expect(SMF64_MAGIC_3).to_equal(0u8)
```

</details>

### smf_extract_executable_stub
_Executable-stub extraction for SMF-as-package loading._

#### extracts an ELF executable stub from a trailer SMF

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = smf_extract_executable_stub(_elf_stub_smf())
expect(stub.is_ok()).to_equal(true)
val bytes = stub.unwrap()
expect(bytes.len()).to_equal(8)
expect(bytes[0]).to_equal(0x7Fu8)
expect(bytes[1]).to_equal(0x45u8)
expect(bytes[2]).to_equal(0x4Cu8)
expect(bytes[3]).to_equal(0x46u8)
```

</details>

#### rejects SMF payloads that do not carry an ELF stub

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = smf_extract_executable_stub(_trailer_magic())
expect(stub.is_err()).to_equal(true)
```

</details>

#### returns typed errors for malformed packages

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = smf_extract_executable_stub(_empty())
expect(stub.is_err()).to_equal(true)
expect(stub.err().unwrap()).to_equal(SMF_ERR_MALFORMED)
```

</details>

#### returns typed errors for wrong role

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val package = _set_header_byte(_elf_stub_smf(), 60, 2u8)
val stub = smf_extract_executable_stub_for_arch(package, Architecture.X86_64)
expect(stub.is_err()).to_equal(true)
expect(stub.err().unwrap()).to_equal(SMF_ERR_WRONG_ROLE)
```

</details>

#### returns typed errors for wrong architecture

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val package = _set_header_byte(_elf_stub_smf(), 61, 5u8)
val stub = smf_extract_executable_stub_for_arch(package, Architecture.X86_64)
expect(stub.is_err()).to_equal(true)
expect(stub.err().unwrap()).to_equal(SMF_ERR_WRONG_ARCH)
```

</details>

#### returns typed errors for ABI mismatch

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val package = _set_header_byte(_elf_stub_smf(), 62, 9u8)
val stub = smf_extract_executable_stub_for_arch(package, Architecture.X86_64)
expect(stub.is_err()).to_equal(true)
expect(stub.err().unwrap()).to_equal(SMF_ERR_ABI_MISMATCH)
```

</details>

#### returns typed errors for missing embedded ELF

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = smf_extract_executable_stub_for_arch(_trailer_magic(), Architecture.X86_64)
expect(stub.is_err()).to_equal(true)
expect(stub.err().unwrap()).to_equal(SMF_ERR_MISSING_ELF)
```

</details>

### smf_extract_library_stub
_Shared-library-stub extraction for SMF dynlib loading._

#### extracts an ELF shared-library stub from a role-2 trailer SMF

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val package = _native_library_stub_smf([0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 2u8, 1u8, 1u8, 0u8])
val stub = smf_extract_library_stub(package)
expect(stub.is_ok()).to_equal(true)
val bytes = stub.unwrap()
expect(bytes.len()).to_equal(8)
expect(bytes[0]).to_equal(0x7Fu8)
expect(bytes[1]).to_equal(0x45u8)
```

</details>

#### extracts a Mach-O shared-library stub from a role-2 trailer SMF

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val package = _native_library_stub_smf([0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 0u8, 0u8, 0u8, 0u8])
val stub = smf_extract_library_stub_for_arch(package, Architecture.Arm64)
expect(stub.is_ok()).to_equal(true)
val bytes = stub.unwrap()
expect(bytes[0]).to_equal(0xCFu8)
expect(bytes[1]).to_equal(0xFAu8)
```

</details>

#### rejects executable role packages as library stubs

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = smf_extract_library_stub(_elf_stub_smf())
expect(stub.is_err()).to_equal(true)
expect(stub.err().unwrap()).to_equal(SMF_ERR_WRONG_ROLE)
```

</details>

#### rejects role-2 packages without native library magic

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val package = _native_library_stub_smf([1u8, 2u8, 3u8, 4u8])
val stub = smf_extract_library_stub(package)
expect(stub.is_err()).to_equal(true)
expect(stub.err().unwrap()).to_equal(SMF_ERR_MISSING_NATIVE_LIBRARY)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

