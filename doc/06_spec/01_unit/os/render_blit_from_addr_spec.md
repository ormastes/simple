# Render Blit From Addr Specification

> Tests covering render_blit_frame_from_addr — bulk copy replaces the per-pixel loop.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Blit From Addr Specification

## Scenarios

### render_blit_frame_from_addr — bulk copy replaces the per-pixel loop

#### lands the same pixels the array path lands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lands the same pixels the array path lands
   - Expected: px_read(0, 0) equals `e00`
   - Expected: px_read(1, 0) equals `e10`
   - Expected: px_read(0, 1) equals `e01`
   - Expected: px_read(1, 1) equals `e11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lands the same pixels the array path lands")
# Stage a source frame by using one shadow buffer as the source, then
# re-init and copy it in. fb_addr = 0 keeps present() a no-op.
render_init(0, 2, 2)
val src = render_shadow_buf()
px_write(0, 0, 0xFF112233u64)
px_write(1, 0, 0xFF445566u64)
px_write(0, 1, 0xFF778899u64)
px_write(1, 1, 0xFFAABBCCu64)

# New shadow buffer; the old one is now just an address holding pixels.
render_init(0, 2, 2)
assert_true(render_shadow_buf() != src)
render_blit_frame_from_addr(src, 4, 2, 2)

val e00: u64 = 0xFF112233
val e10: u64 = 0xFF445566
val e01: u64 = 0xFF778899
val e11: u64 = 0xFFAABBCC
expect(px_read(0, 0)).to_equal(e00)
expect(px_read(1, 0)).to_equal(e10)
expect(px_read(0, 1)).to_equal(e01)
expect(px_read(1, 1)).to_equal(e11)
```

</details>

#### charges zero per-pixel FFI stores, and exactly one bulk copy

- charges zero per-pixel FFI stores, and exactly one bulk copy
   - Expected: render_blit_scalar_pixel_writes() equals `zero`
   - Expected: render_blit_bulk_copies() equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("charges zero per-pixel FFI stores, and exactly one bulk copy")
render_init(0, 2, 2)
val src = render_shadow_buf()
px_write(0, 0, 0xFF010203u64)
px_write(1, 0, 0xFF040506u64)
px_write(0, 1, 0xFF070809u64)
px_write(1, 1, 0xFF0A0B0Cu64)

render_init(0, 2, 2)
render_blit_counters_reset()
render_blit_frame_from_addr(src, 4, 2, 2)

# THE GATE. 0 scalar stores is the whole point of this function.
val zero: u64 = 0
val one: u64 = 1
expect(render_blit_scalar_pixel_writes()).to_equal(zero)
expect(render_blit_bulk_copies()).to_equal(one)
```

</details>

#### proves the counter is live: the array path DOES charge per-pixel stores

- proves the counter is live: the array path DOES charge per-pixel stores
   - Expected: render_blit_scalar_pixel_writes() equals `four`
   - Expected: render_blit_bulk_copies() equals `zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("proves the counter is live: the array path DOES charge per-pixel stores")
# Anti-vacuity control. If this example ever reports 0 too, the counter
# is broken and the gate above proves nothing.
render_init(0, 2, 2)
render_blit_counters_reset()
val pixels: [u32] = [0xFF112233u32, 0xFF445566u32, 0xFF778899u32, 0xFFAABBCCu32]
render_blit_frame(pixels, 2, 2)
val four: u64 = 4
val zero: u64 = 0
expect(render_blit_scalar_pixel_writes()).to_equal(four)
expect(render_blit_bulk_copies()).to_equal(zero)
```

</details>

#### clamps an over-large source to framebuffer capacity without overrun

- clamps an over-large source to framebuffer capacity without overrun
   - Expected: px_read(0, 0) equals `a`
   - Expected: px_read(1, 0) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps an over-large source to framebuffer capacity without overrun")
render_init(0, 4, 1)
val src = render_shadow_buf()
px_write(0, 0, 0xFF010101u64)
px_write(1, 0, 0xFF020202u64)
px_write(2, 0, 0xFF030303u64)
px_write(3, 0, 0xFF040404u64)

# Destination is only 2x1; asking for 4x1 must copy 2 pixels, not 4.
render_init(0, 2, 1)
render_blit_frame_from_addr(src, 4, 4, 1)
val a: u64 = 0xFF010101
val b: u64 = 0xFF020202
expect(px_read(0, 0)).to_equal(a)
expect(px_read(1, 0)).to_equal(b)
```

</details>

#### refuses a null source address instead of copying from address zero

- refuses a null source address instead of copying from address zero
   - Expected: render_blit_bulk_copies() equals `zero`
   - Expected: px_read(0, 0) equals `keep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a null source address instead of copying from address zero")
render_init(0, 2, 2)
px_write(0, 0, 0xFFDEAD00u64)
render_blit_counters_reset()
render_blit_frame_from_addr(0, 4, 2, 2)
# Nothing copied, nothing clobbered.
val zero: u64 = 0
val keep: u64 = 0xFFDEAD00
expect(render_blit_bulk_copies()).to_equal(zero)
expect(px_read(0, 0)).to_equal(keep)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/render_blit_from_addr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering render_blit_frame_from_addr — bulk copy replaces the per-pixel loop.
- render_blit_frame_from_addr — bulk copy replaces the per-pixel loop

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `24cf7aee7af19e17cac3e9ccfdbf5084156c493edbe66ef4c05e988d1e6ea348`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24cf7aee7af19e17cac3e9ccfdbf5084156c493edbe66ef4c05e988d1e6ea348`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24cf7aee7af19e17cac3e9ccfdbf5084156c493edbe66ef4c05e988d1e6ea348`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/render_blit_from_addr_spec.spl
mirror: doc/06_spec/01_unit/os/render_blit_from_addr_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/render_blit_from_addr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/render_blit_from_addr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/render_blit_from_addr_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lands the same pixels the array path lands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/render_blit_from_addr_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'charges zero per-pixel FFI stores, and exactly one bulk copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/render_blit_from_addr_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves the counter is live: the array path DOES charge per-pixel stores' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
