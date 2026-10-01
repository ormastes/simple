# game2d.render.evidence — pixel-evidence oracle unit specs

> Direct unit specs for the pixel-evidence oracles extracted from Rollball

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# game2d.render.evidence — pixel-evidence oracle unit specs

Direct unit specs for the pixel-evidence oracles extracted from Rollball

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | src/lib/nogc_async_mut/game2d/render/evidence.spl |
| Source | `test/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Direct unit specs for the pixel-evidence oracles extracted from Rollball
(`find_centroid`, `diff_count`, `dump_ppm`): absolute expected values on
small, hand-constructed pixel buffers — no rendering, no game state.

## Scenarios

### game2d.render.evidence — find_centroid

#### single marked pixel in a 4x4 buffer returns its exact coordinates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- single marked pixel in a 4x4 buffer returns its exact coordinates


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single marked pixel in a 4x4 buffer returns its exact coordinates")
val bg: u32 = 0xFF000000
val mark: u32 = 0xFFFF0000
var px: [u32] = [bg; 16]
px[1 * 4 + 2] = mark
val c = find_centroid(px, 4, 4, mark)
assert_equal(c[0], 2)
assert_equal(c[1], 1)
assert_equal(c[2], 1)
```

</details>

#### two marked pixels average to the exact integer centroid

- two marked pixels average to the exact integer centroid


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two marked pixels average to the exact integer centroid")
val bg: u32 = 0xFF000000
val mark: u32 = 0xFF00FF00
var px: [u32] = [bg; 16]
px[0 * 4 + 0] = mark
px[3 * 4 + 2] = mark
val c = find_centroid(px, 4, 4, mark)
assert_equal(c[0], 1)
assert_equal(c[1], 1)
assert_equal(c[2], 2)
```

</details>

#### no matching pixel returns the [-1, -1, 0] sentinel

- no matching pixel returns the [-1, -1, 0] sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no matching pixel returns the [-1, -1, 0] sentinel")
val bg: u32 = 0xFF000000
var px: [u32] = [bg; 16]
val c = find_centroid(px, 4, 4, 0xFFFFFFFF)
assert_equal(c[0], -1)
assert_equal(c[1], -1)
assert_equal(c[2], 0)
```

</details>

### game2d.render.evidence — diff_count

#### counts the exact number of differing pixels

- counts the exact number of differing pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts the exact number of differing pixels")
var a: [u32] = [0; 16]
var b: [u32] = [0; 16]
b[0] = 1
b[5] = 1
b[15] = 1
assert_equal(diff_count(a, b, 16), 3)
```

</details>

#### identical buffers diff to exactly zero

- identical buffers diff to exactly zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identical buffers diff to exactly zero")
var a: [u32] = [7; 16]
var b: [u32] = [7; 16]
assert_equal(diff_count(a, b, 16), 0)
```

</details>

### game2d.render.evidence — dump_ppm

#### writes an exact P3 header and pixel bytes for a known 2x1 buffer

- writes an exact P3 header and pixel bytes for a known 2x1 buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes an exact P3 header and pixel bytes for a known 2x1 buffer")
val _ = rt_dir_create("build/test-scratch", true)
val path = "build/test-scratch/evidence_dump_ppm_spec.ppm"
val px: [u32] = [0xFFFF0000, 0xFF00FF00]
assert_true(dump_ppm(path, px, 2, 1))
assert_true(file_exists(path))
val content = file_read(path)
assert_equal(content, "P3\n2 1\n255\n255 0 0\n0 255 0\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `src/lib/nogc_async_mut/game2d/render/evidence.spl`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d96dd893c58eb4f463ee49c531b0cc4d7d5c34a647d72962061e757141b7ec7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d96dd893c58eb4f463ee49c531b0cc4d7d5c34a647d72962061e757141b7ec7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d96dd893c58eb4f463ee49c531b0cc4d7d5c34a647d72962061e757141b7ec7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single marked pixel in a 4x4 buffer returns its exact coordinates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two marked pixels average to the exact integer centroid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no matching pixel returns the [-1, -1, 0] sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
