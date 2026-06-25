# smf_bounds_spec

> SMF Loader — bounds-check unit specs.

<!-- sdn-diagram:id=smf_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_bounds_spec -> std
smf_bounds_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_bounds_spec

SMF Loader — bounds-check unit specs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FS-EXEC-MULTIARCH-AC3 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/smf_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SMF Loader — bounds-check unit specs.
Verifies that _smf_copy_range (via smf_extract_executable_stub) fails closed
on truncated images and out-of-range sizes, and that the in_range guard in
byte_utils rejects overflow/negative inputs.

## Scenarios

### in_range bounds guard

#### accepts a zero-size range at offset zero

- data push
   - Expected: in_range(data, 0i64, 0i64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(0u8)
expect(in_range(data, 0i64, 0i64)).to_equal(true)
```

</details>

#### accepts a range that exactly fills the buffer

- data push
- data push
- data push
   - Expected: in_range(data, 0i64, 3i64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(1u8)
data.push(2u8)
data.push(3u8)
expect(in_range(data, 0i64, 3i64)).to_equal(true)
```

</details>

#### rejects a range that exceeds the buffer

- data push
- data push
   - Expected: in_range(data, 0i64, 3i64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(1u8)
data.push(2u8)
expect(in_range(data, 0i64, 3i64)).to_equal(false)
```

</details>

#### rejects a negative offset

- data push
   - Expected: in_range(data, -1i64, 1i64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(1u8)
expect(in_range(data, -1i64, 1i64)).to_equal(false)
```

</details>

#### rejects a negative size

- data push
   - Expected: in_range(data, 0i64, -1i64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(1u8)
expect(in_range(data, 0i64, -1i64)).to_equal(false)
```

</details>

#### rejects an empty buffer with nonzero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
expect(in_range(data, 0i64, 1i64)).to_equal(false)
```

</details>

### smf_extract_executable_stub — truncated image

#### rejects an image where stub_size exceeds bytes before the trailer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# declared stub_size=16 but only 4 ELF bytes precede the trailer
# stub_size(16) > header_offset(4) so callers return SMF_ERR_MALFORMED
val bytes = _truncated_smf(16i64, 4i64)
val result = smf_extract_executable_stub(bytes)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_equal(SMF_ERR_MALFORMED)
```

</details>

<details>
<summary>Advanced: rejects an image where the entire buffer is just the trailer (no room for stub)</summary>

#### rejects an image where the entire buffer is just the trailer (no room for stub)

- var trailer =  make trailer
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# stub_size=8 but header_offset=0 (trailer at offset 0, no leading bytes)
var trailer = _make_trailer(0x1000i64, 8i64)
# set stub_size to non-zero
trailer[52] = 8u8
val result = smf_extract_executable_stub(trailer)
expect(result.is_err()).to_equal(true)
```

</details>


</details>

#### accepts a well-formed SMF with a valid ELF stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _smf_with_elf_stub(8i64)
val result = smf_extract_executable_stub(bytes)
expect(result.is_ok()).to_equal(true)
val stub = result.unwrap()
expect(stub.len()).to_equal(8)
expect(stub[0]).to_equal(0x7Fu8)
```

</details>

### smf_extract_executable_stub — zero stub_size

#### returns SMF_ERR_MISSING_ELF when stub_size is zero

- var trailer =  make trailer
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap() equals `SMF_ERR_MISSING_ELF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# _make_trailer with stub_size=0 means no ELF stub declared
var trailer = _make_trailer(0x1000i64, 0i64)
val result = smf_extract_executable_stub(trailer)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_equal(SMF_ERR_MISSING_ELF)
```

</details>

### smf_extract_executable_stub_for_arch — truncated image arch-checked

#### rejects truncated image on x86_64 arch check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _truncated_smf(32i64, 4i64)
val result = smf_extract_executable_stub_for_arch(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects truncated image on arm64 arch check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _truncated_smf(32i64, 4i64)
val result = smf_extract_executable_stub_for_arch(bytes, Architecture.Arm64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects truncated image on riscv64 arch check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _truncated_smf(32i64, 4i64)
val result = smf_extract_executable_stub_for_arch(bytes, Architecture.Riscv64)
expect(result.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
