# Limine Boot Framebuffer Validation Specification

> Tests `limine_framebuffer_fields_valid`, the pure sanity check `_parse_framebuffer` applies to the raw Limine framebuffer descriptor before trusting it. Garbage width/height/bpp/pitch/address must be rejected so the caller falls back to the existing no-framebuffer path instead of driving a bogus scanout.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Limine Boot Framebuffer Validation Specification

Tests `limine_framebuffer_fields_valid`, the pure sanity check `_parse_framebuffer` applies to the raw Limine framebuffer descriptor before trusting it. Garbage width/height/bpp/pitch/address must be rejected so the caller falls back to the existing no-framebuffer path instead of driving a bogus scanout.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-BOOT |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/limine_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests `limine_framebuffer_fields_valid`, the pure sanity check `_parse_framebuffer`
applies to the raw Limine framebuffer descriptor before trusting it. Garbage
width/height/bpp/pitch/address must be rejected so the caller falls back to
the existing no-framebuffer path instead of driving a bogus scanout.

## Scenarios

### limine_framebuffer_fields_valid

#### accepts a typical 1280x800x32 descriptor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a typical 1280x800x32 descriptor
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0xC0000000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a typical 1280x800x32 descriptor")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0xC0000000)).to_equal(true)
```

</details>

#### accepts a 24bpp descriptor with exact pitch

- accepts a 24bpp descriptor with exact pitch
   - Expected: limine_framebuffer_fields_valid(640, 480, 1920, 24, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a 24bpp descriptor with exact pitch")
expect(limine_framebuffer_fields_valid(640, 480, 1920, 24, 0x1000)).to_equal(true)
```

</details>

#### accepts the exact 16384 ceiling

- accepts the exact 16384 ceiling
   - Expected: limine_framebuffer_fields_valid(16384, 16384, 65536, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the exact 16384 ceiling")
expect(limine_framebuffer_fields_valid(16384, 16384, 65536, 32, 0x1000)).to_equal(true)
```

</details>

#### accepts a pitch larger than the minimum (row padding/alignment)

- accepts a pitch larger than the minimum (row padding/alignment)
   - Expected: limine_framebuffer_fields_valid(1280, 800, 8192, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a pitch larger than the minimum (row padding/alignment)")
expect(limine_framebuffer_fields_valid(1280, 800, 8192, 32, 0x1000)).to_equal(true)
```

</details>

#### rejects a zero address, otherwise-valid fields

- rejects a zero address, otherwise-valid fields
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a zero address, otherwise-valid fields")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0))
```

</details>

#### rejects zero width, otherwise-valid fields

- rejects zero width, otherwise-valid fields
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero width, otherwise-valid fields")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(0, 800, 5120, 32, 0x1000))
```

</details>

#### rejects zero height, otherwise-valid fields

- rejects zero height, otherwise-valid fields
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero height, otherwise-valid fields")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(1280, 0, 5120, 32, 0x1000))
```

</details>

#### rejects width above the 16384 ceiling

- rejects width above the 16384 ceiling
   - Expected: limine_framebuffer_fields_valid(16384, 800, 65536, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects width above the 16384 ceiling")
expect(limine_framebuffer_fields_valid(16384, 800, 65536, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(16385, 800, 65540, 32, 0x1000))
```

</details>

#### rejects height above the 16384 ceiling

- rejects height above the 16384 ceiling
   - Expected: limine_framebuffer_fields_valid(1280, 16384, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects height above the 16384 ceiling")
expect(limine_framebuffer_fields_valid(1280, 16384, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(1280, 16385, 5120, 32, 0x1000))
```

</details>

#### rejects an unsupported bpp of 16

- rejects an unsupported bpp of 16
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unsupported bpp of 16")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(1280, 800, 2560, 16, 0x1000))
```

</details>

#### rejects an unsupported bpp of 0 (garbage descriptor)

- rejects an unsupported bpp of 0 (garbage descriptor)
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unsupported bpp of 0 (garbage descriptor)")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(1280, 800, 5120, 0, 0x1000))
```

</details>

#### rejects a pitch smaller than one scanline at 32bpp

- rejects a pitch smaller than one scanline at 32bpp
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a pitch smaller than one scanline at 32bpp")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(1280, 800, 100, 32, 0x1000))
```

</details>

#### rejects an all-zero garbage descriptor

- rejects an all-zero garbage descriptor
   - Expected: limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an all-zero garbage descriptor")
expect(limine_framebuffer_fields_valid(1280, 800, 5120, 32, 0x1000)).to_equal(true)
assert_false(limine_framebuffer_fields_valid(0, 0, 0, 0, 0))
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f187dd6199ee79c713f0af60ac1b1ae7c311cd6d07b2251b0591a7bb9f39b79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f187dd6199ee79c713f0af60ac1b1ae7c311cd6d07b2251b0591a7bb9f39b79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f187dd6199ee79c713f0af60ac1b1ae7c311cd6d07b2251b0591a7bb9f39b79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/boot/limine_boot_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/limine_boot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/boot/limine_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/limine_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/boot/limine_boot_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a typical 1280x800x32 descriptor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/limine_boot_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a 24bpp descriptor with exact pitch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/limine_boot_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the exact 16384 ceiling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
