# Riscv Noalloc Dtb Capability Specification

> Tests covering boot-owned RV64 DTB capability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Noalloc Dtb Capability Specification

## Scenarios

### boot-owned RV64 DTB capability

#### decodes enabled unique harts and makes the observed boot hart logical zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes enabled unique harts and makes the observed boot hart logical zero
   - Expected: riscv_noalloc_dtb_capability_valid() is true
   - Expected: riscv_noalloc_dtb_hart_count() equals `2u32`
   - Expected: riscv_noalloc_dtb_hart_id(0u32) equals `3u64`
   - Expected: riscv_noalloc_dtb_hart_id(1u32) equals `7u64`
   - Expected: riscv_noalloc_dtb_has_zicbom() is true
   - Expected: riscv_noalloc_dtb_cache_stride() equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
# @req REQ-SSPEC-UNIT
step("decodes enabled unique harts and makes the observed boot hart logical zero")
val blob = _encoded_dtb(7u32, 3u32, true, "rv64imafdc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
_install(blob, 0x10000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x10000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(true)
expect(riscv_noalloc_dtb_hart_count()).to_equal(2u32)
expect(riscv_noalloc_dtb_hart_id(0u32)).to_equal(3u64)
expect(riscv_noalloc_dtb_hart_id(1u32)).to_equal(7u64)
expect(riscv_noalloc_dtb_has_zicbom()).to_equal(true)
expect(riscv_noalloc_dtb_cache_stride()).to_equal(64u32)
```

</details>

#### excludes disabled CPUs from the capability intersection

- excludes disabled CPUs from the capability intersection
   - Expected: riscv_noalloc_dtb_hart_count() equals `1u32`
   - Expected: riscv_noalloc_dtb_has_zicbom() is true
   - Expected: riscv_noalloc_dtb_cache_stride() equals `128u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("excludes disabled CPUs from the capability intersection")
val blob = _encoded_dtb(3u32, 7u32, false, "rv64gc_zicbom", "rv64gc", 128u32, 0u32)
_install(blob, 0x20000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x20000u64)
expect(riscv_noalloc_dtb_hart_count()).to_equal(1u32)
expect(riscv_noalloc_dtb_has_zicbom()).to_equal(true)
expect(riscv_noalloc_dtb_cache_stride()).to_equal(128u32)
```

</details>

#### requires the exact zicbom token on every enabled CPU

- requires the exact zicbom token on every enabled CPU
   - Expected: riscv_noalloc_dtb_has_zicbom() is false
   - Expected: riscv_noalloc_dtb_cache_stride() equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires the exact zicbom token on every enabled CPU")
val blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbomx", "rv64gc_zicbom", 64u32, 64u32)
_install(blob, 0x30000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x30000u64)
expect(riscv_noalloc_dtb_has_zicbom()).to_equal(false)
expect(riscv_noalloc_dtb_cache_stride()).to_equal(64u32)
```

</details>

#### fails closed for duplicate enabled hart IDs

- fails closed for duplicate enabled hart IDs
   - Expected: riscv_noalloc_dtb_capability_valid() is false
   - Expected: riscv_noalloc_dtb_hart_count() equals `1u32`
   - Expected: riscv_noalloc_dtb_hart_id(0u32) equals `3u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed for duplicate enabled hart IDs")
val blob = _encoded_dtb(3u32, 3u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
_install(blob, 0x40000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x40000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
expect(riscv_noalloc_dtb_hart_count()).to_equal(1u32)
expect(riscv_noalloc_dtb_hart_id(0u32)).to_equal(3u64)
```

</details>

#### fails closed when enabled CPUs exceed fixed census capacity

- fails closed when enabled CPUs exceed fixed census capacity
   - Expected: riscv_noalloc_dtb_capability_valid() is false
   - Expected: riscv_noalloc_dtb_hart_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed when enabled CPUs exceed fixed census capacity")
val blob = _encoded_many_dtb(33u32)
_install(blob, 0x48000u64)
riscv_noalloc_dtb_capability_init(0u64, 0x48000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
expect(riscv_noalloc_dtb_hart_count()).to_equal(1u32)
```

</details>

#### fails closed for inconsistent power-of-two block sizes

- fails closed for inconsistent power-of-two block sizes
   - Expected: riscv_noalloc_dtb_capability_valid() is false
   - Expected: riscv_noalloc_dtb_has_zicbom() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed for inconsistent power-of-two block sizes")
val blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 128u32)
_install(blob, 0x50000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x50000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
expect(riscv_noalloc_dtb_has_zicbom()).to_equal(false)
```

</details>

#### fails closed for a consistent non-power-of-two block size

- fails closed for a consistent non-power-of-two block size
   - Expected: riscv_noalloc_dtb_capability_valid() is false
   - Expected: riscv_noalloc_dtb_cache_stride() equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed for a consistent non-power-of-two block size")
val blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 96u32, 96u32)
_install(blob, 0x58000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x58000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
expect(riscv_noalloc_dtb_cache_stride()).to_equal(64u32)
```

</details>

#### fails closed when firmware omits the observed boot hart

- fails closed when firmware omits the observed boot hart
   - Expected: riscv_noalloc_dtb_capability_valid() is false
   - Expected: riscv_noalloc_dtb_hart_id(0u32) equals `19u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed when firmware omits the observed boot hart")
val blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
_install(blob, 0x5c000u64)
riscv_noalloc_dtb_capability_init(19u64, 0x5c000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
expect(riscv_noalloc_dtb_hart_id(0u32)).to_equal(19u64)
```

</details>

#### uses the observed boot hart fallback for malformed headers

- uses the observed boot hart fallback for malformed headers
   - Expected: riscv_noalloc_dtb_capability_valid() is false
   - Expected: riscv_noalloc_dtb_hart_id(0u32) equals `19u64`
   - Expected: riscv_noalloc_dtb_cache_stride() equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses the observed boot hart fallback for malformed headers")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
blob[0] = 0u8
_install(blob, 0x60000u64)
riscv_noalloc_dtb_capability_init(19u64, 0x60000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
expect(riscv_noalloc_dtb_hart_id(0u32)).to_equal(19u64)
expect(riscv_noalloc_dtb_cache_stride()).to_equal(64u32)
```

</details>

#### rejects incompatible header versions

- rejects incompatible header versions
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects incompatible header versions")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
blob = _poke32(blob, 20, 16u32)
_install(blob, 0x64000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x64000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects overlapping structure and strings ranges

- rejects overlapping structure and strings ranges
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects overlapping structure and strings ranges")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
blob = _poke32(blob, 12, _peek32(blob, 8))
_install(blob, 0x65000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x65000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects a structure block without a valid END token

- rejects a structure block without a valid END token
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a structure block without a valid END token")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
val strings_offset = _peek32(blob, 12) as i64
blob = _poke32(blob, strings_offset - 4, 0u32)
_install(blob, 0x66000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x66000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects a depth-zero property after the root closes

- rejects a depth-zero property after the root closes
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a depth-zero property after the root closes")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
val strings_offset = _peek32(blob, 12) as i64
blob = _poke32(blob, strings_offset - 4, 3u32)
_install(blob, 0x66400u64)
riscv_noalloc_dtb_capability_init(3u64, 0x66400u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### requires both cpus cell-width properties

- requires both cpus cell-width properties
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires both cpus cell-width properties")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
val size_prop = _find_prop(blob, 4u32, 58u32)
blob = _poke32(blob, size_prop + 8, 21u32)
_install(blob, 0x66600u64)
riscv_noalloc_dtb_capability_init(3u64, 0x66600u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects duplicate relevant CPU properties

- rejects duplicate relevant CPU properties
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects duplicate relevant CPU properties")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
val cbom_prop = _find_prop(blob, 4u32, 21u32)
blob = _poke32(blob, cbom_prop + 8, 0u32)
_install(blob, 0x66700u64)
riscv_noalloc_dtb_capability_init(3u64, 0x66700u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects an unsupported CPU address-cell width

- rejects an unsupported CPU address-cell width
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an unsupported CPU address-cell width")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
blob = _poke32(blob, 88, 3u32)
_install(blob, 0x66800u64)
riscv_noalloc_dtb_capability_init(3u64, 0x66800u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects malformed status string length and termination

- rejects malformed status string length and termination
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects malformed status string length and termination")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
val status = _find_text(blob, "okay")
blob[status + 4] = 1u8
_install(blob, 0x67000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x67000u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects an ISA property without its terminating NUL

- rejects an ISA property without its terminating NUL
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an ISA property without its terminating NUL")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
val isa = _find_text(blob, "rv64gc_zicbom")
blob[isa + 14] = 1u8
_install(blob, 0x67800u64)
riscv_noalloc_dtb_capability_init(3u64, 0x67800u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### does not admit CPU nodes outside the root cpus child

- does not admit CPU nodes outside the root cpus child
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not admit CPU nodes outside the root cpus child")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
val cpus = _find_text(blob, "cpus")
blob[cpus] = 120u8
_install(blob, 0x67c00u64)
riscv_noalloc_dtb_capability_init(3u64, 0x67c00u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### rejects physical-address overflow before reading a header

- rejects physical-address overflow before reading a header
   - Expected: riscv_noalloc_dtb_capability_valid() is false
   - Expected: riscv_noalloc_dtb_hart_id(0u32) equals `23u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects physical-address overflow before reading a header")
mmio_reset_for_test()
riscv_noalloc_dtb_capability_init(23u64, 0xfffffffffffffff0u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
expect(riscv_noalloc_dtb_hart_id(0u32)).to_equal(23u64)
```

</details>

#### scans reservation entries until a zero address and size terminator

- scans reservation entries until a zero address and size terminator
   - Expected: riscv_noalloc_dtb_capability_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("scans reservation entries until a zero address and size terminator")
var blob = _encoded_dtb(3u32, 7u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
blob = _poke32(blob, 44, 1u32)
_install(blob, 0x67400u64)
riscv_noalloc_dtb_capability_init(3u64, 0x67400u64)
expect(riscv_noalloc_dtb_capability_valid()).to_equal(false)
```

</details>

#### preserves sparse hart IDs above one SBI mask window

- preserves sparse hart IDs above one SBI mask window
   - Expected: riscv_noalloc_dtb_hart_id(0u32) equals `130u64`
   - Expected: window.1 equals `128u64`
   - Expected: window.0 equals `4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves sparse hart IDs above one SBI mask window")
val blob = _encoded_dtb(130u32, 3u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
_install(blob, 0x68000u64)
riscv_noalloc_dtb_capability_init(130u64, 0x68000u64)
expect(riscv_noalloc_dtb_hart_id(0u32)).to_equal(130u64)
val window = hal_smp_ipi_window(riscv_noalloc_dtb_hart_id(0u32))
expect(window.1).to_equal(128u64)
expect(window.0).to_equal(4u64)
```

</details>

#### passes the sparse physical hart ID to the HSM target decision

- passes the sparse physical hart ID to the HSM target decision
   - Expected: target.0 is true
   - Expected: target.1 equals `130u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("passes the sparse physical hart ID to the HSM target decision")
val blob = _encoded_dtb(3u32, 130u32, true, "rv64gc_zicbom", "rv64gc_zicbom", 64u32, 64u32)
_install(blob, 0x6c000u64)
riscv_noalloc_dtb_capability_init(3u64, 0x6c000u64)
val target = hal_smp_hsm_target(1u32)
expect(target.0).to_equal(true)
expect(target.1).to_equal(130u64)
```

</details>

#### keeps both handoff paths ordered before readiness publication

- keeps both handoff paths ordered before readiness publication


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps both handoff paths ordered before readiness publication")
val source = read_file_text("src/os/kernel/boot/riscv_noalloc_handoff.spl")
expect(source).to_contain("g_riscv_boot_dtb_addr = dtb_addr\n    riscv_noalloc_dtb_capability_init(hart_id, dtb_addr)")
expect(source).to_contain("riscv_noalloc_dtb_capability_init(hart_id, dtb_addr)\n    g_riscv_ram_base")
expect(source).to_contain("g_riscv_noalloc_handoff_ready = true")
```

</details>

#### statically pins bounded storage and prohibited-surface absence

- statically pins bounded storage and prohibited-surface absence
   - Expected: source_lacks(source, "extern fn") is true
   - Expected: source_lacks(source, "extern fn rt_") is true
   - Expected: source_lacks(source, "Option<") is true
   - Expected: source_lacks(source, "Result<") is true
   - Expected: source_lacks(source, "var _g_rv64_dtb_harts: [u64]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("statically pins bounded storage and prohibited-surface absence")
val source = read_file_text("src/os/kernel/boot/riscv_noalloc_dtb_capability.spl")
expect(source).to_contain("[u64; 32]")
expect(source).to_contain("_FDT_MAX_SIZE: u64 = 0x00200000u64")
expect(source).to_contain("_FDT_MAX_DEPTH: u32 = 32u32")
expect(source_lacks(source, "extern fn")).to_equal(true)
expect(source_lacks(source, "extern fn rt_")).to_equal(true)
expect(source_lacks(source, "Option<")).to_equal(true)
expect(source_lacks(source, "Result<")).to_equal(true)
expect(source_lacks(source, "var _g_rv64_dtb_harts: [u64]")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering boot-owned RV64 DTB capability.
- boot-owned RV64 DTB capability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78b4989b38760d00efed74fb0e9c1973fce6768fab966eb920ec4ba55568a3d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78b4989b38760d00efed74fb0e9c1973fce6768fab966eb920ec4ba55568a3d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78b4989b38760d00efed74fb0e9c1973fce6768fab966eb920ec4ba55568a3d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes enabled unique harts and makes the observed boot hart logical zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.spl:222:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes disabled CPUs from the capability intersection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/riscv_noalloc_dtb_capability_spec.spl:232:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the exact zicbom token on every enabled CPU' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
