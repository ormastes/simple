# Nvfs 32bit Layout Specification

> Tests covering AC-3/R5 — NVFS superblock byte-equal across archs, AC-3/R5 — superblock layout is fixed-width 64-bit, AC-3/R5 — 32-bit kernel rejects extents > 4 GiB.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs 32bit Layout Specification

## Scenarios

### AC-3/R5 — NVFS superblock byte-equal across archs

#### x86_64 superblock dump exists

- x86_64 superblock dump exists
   - Expected: file_exists(SUPERBLOCK_X86) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64 superblock dump exists")
expect(file_exists(SUPERBLOCK_X86)).to_equal(true)
```

</details>

#### riscv32 superblock dump exists

- riscv32 superblock dump exists
   - Expected: file_exists(SUPERBLOCK_RV32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32 superblock dump exists")
expect(file_exists(SUPERBLOCK_RV32)).to_equal(true)
```

</details>

#### parity report exists

- parity report exists
   - Expected: file_exists(PARITY_REPORT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity report exists")
expect(file_exists(PARITY_REPORT)).to_equal(true)
```

</details>

#### parity report flags byte-equal = true

- parity report flags byte-equal = true
   - Expected: r contains `"byte_equal": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity report flags byte-equal = true")
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"byte_equal\": true")).to_equal(true)
```

</details>

#### parity report records both file SHA-256 hashes

- parity report records both file SHA-256 hashes
   - Expected: r contains `"x86_64_sha256"`
   - Expected: r contains `"riscv32_sha256"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity report records both file SHA-256 hashes")
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"x86_64_sha256\"")).to_equal(true)
expect(r.contains("\"riscv32_sha256\"")).to_equal(true)
```

</details>

#### parity report shows identical SHA-256

- parity report shows identical SHA-256
   - Expected: r contains `"sha256_match": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity report shows identical SHA-256")
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"sha256_match\": true")).to_equal(true)
```

</details>

### AC-3/R5 — superblock layout is fixed-width 64-bit

#### superblock bytes are non-empty

- superblock bytes are non-empty
   - Expected: bytes.length() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("superblock bytes are non-empty")
val bytes: [u8] = file_read_bytes(SUPERBLOCK_X86)
expect(bytes.length() > 0).to_equal(true)
```

</details>

#### superblock bytes length is the locked fixed size

- superblock bytes length is the locked fixed size
   - Expected: r contains `"superblock_size_locked": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("superblock bytes length is the locked fixed size")
"""Phase 3 §7.2 locked superblock length. The exact value is
embedded in the report; assert match."""
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"superblock_size_locked\": true")).to_equal(true)
```

</details>

### AC-3/R5 — 32-bit kernel rejects extents > 4 GiB

#### overflow report exists

- overflow report exists
   - Expected: file_exists(OVERFLOW_REPORT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overflow report exists")
expect(file_exists(OVERFLOW_REPORT)).to_equal(true)
```

</details>

#### riscv32 path returns PointerTooLarge for >4GiB extent

- riscv32 path returns PointerTooLarge for >4GiB extent
   - Expected: r contains `"riscv32_pointer_too_large": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32 path returns PointerTooLarge for >4GiB extent")
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"riscv32_pointer_too_large\": true")).to_equal(true)
```

</details>

#### i686 path returns PointerTooLarge for >4GiB extent

- i686 path returns PointerTooLarge for >4GiB extent
   - Expected: r contains `"i686_pointer_too_large": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i686 path returns PointerTooLarge for >4GiB extent")
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"i686_pointer_too_large\": true")).to_equal(true)
```

</details>

#### armv7 path returns PointerTooLarge for >4GiB extent

- armv7 path returns PointerTooLarge for >4GiB extent
   - Expected: r contains `"armv7_pointer_too_large": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("armv7 path returns PointerTooLarge for >4GiB extent")
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"armv7_pointer_too_large\": true")).to_equal(true)
```

</details>

#### 64-bit archs accept >4GiB extents

- 64-bit archs accept >4GiB extents
   - Expected: r contains `"x86_64_large_extent_ok": true`
   - Expected: r contains `"aarch64_large_extent_ok": true`
   - Expected: r contains `"riscv64_large_extent_ok": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("64-bit archs accept >4GiB extents")
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"x86_64_large_extent_ok\": true")).to_equal(true)
expect(r.contains("\"aarch64_large_extent_ok\": true")).to_equal(true)
expect(r.contains("\"riscv64_large_extent_ok\": true")).to_equal(true)
```

</details>

#### Result.Err path is taken — no panic

- Result.Err path is taken — no panic
   - Expected: r contains `"panicked": false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Result.Err path is taken — no panic")
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"panicked\": false")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/multiarch/nvfs_32bit_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-3/R5 — NVFS superblock byte-equal across archs, AC-3/R5 — superblock layout is fixed-width 64-bit, AC-3/R5 — 32-bit kernel rejects extents > 4 GiB.
- AC-3/R5 — NVFS superblock byte-equal across archs
- AC-3/R5 — superblock layout is fixed-width 64-bit
- AC-3/R5 — 32-bit kernel rejects extents > 4 GiB

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f0517fa174a0bdf606897a3d05f1f9f47e13bd5d7d3290c0ce4eb2554b788f7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f0517fa174a0bdf606897a3d05f1f9f47e13bd5d7d3290c0ce4eb2554b788f7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f0517fa174a0bdf606897a3d05f1f9f47e13bd5d7d3290c0ce4eb2554b788f7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/multiarch/nvfs_32bit_layout_spec.spl
mirror: doc/06_spec/unit/os/multiarch/nvfs_32bit_layout_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/multiarch/nvfs_32bit_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/multiarch/nvfs_32bit_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/multiarch/nvfs_32bit_layout_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/unit/os/multiarch/nvfs_32bit_layout_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x86_64 superblock dump exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/nvfs_32bit_layout_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'riscv32 superblock dump exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/nvfs_32bit_layout_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parity report exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
