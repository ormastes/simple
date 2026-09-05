# The GPU Provenance Predicate, Pinned By Value

> A frame may be labelled GPU-rendered only when the readback proves a device produced it. All four conjuncts are load-bearing:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# The GPU Provenance Predicate, Pinned By Value

A frame may be labelled GPU-rendered only when the readback proves a device produced it. All four conjuncts are load-bearing:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A frame may be labelled GPU-rendered only when the readback proves a device
produced it. All four conjuncts are load-bearing:

    source == "device_readback" and backend_handle > 0
        and device_identity > 0 and pixel_count == frame_pixels

Until now this predicate was only ever observed *indirectly*, through the
presenter's decision string. A decision string can stay word-for-word identical
while the predicate behind it is quietly loosened, so this spec pins the
predicate itself by value via `web_gpu_readback_device_proven_for_frame`, with
one arm per conjunct. Dropping any single conjunct turns an arm red.

The `pixel_count` conjunct is the anti-truncation one: it is what stops a short
or fallback buffer from being certified as a device frame.

## Measured note on the width of the comparison

`pixel_count` is an i64 field while the frame extent is two i32s, so the product
`width * height` is computed with `.to_i64()` at every call site. This is
defence-in-depth, **not** a fix for an observed defect: it was measured on this
engine that a value declared `i32` does **not** wrap at 32 bits —
`65540 * 65536` evaluates to `4295229440` exactly, not to the 32-bit-wrapped
`262144` (probe: `simple run` on a two-line `w * h` function). An inversion in
which a truncated 262144-pixel readback out-certifies the honest full one is
therefore **not reachable on the current engine**, and the arm below that
exercises that extent is recorded as **non-biting today** — it is a tripwire for
a backend where i32 really is 32-bit (native codegen), not evidence of a
present-day bug. The arms that do bite are the four conjunct arms.

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### GPU provenance predicate

#### certifies a complete device readback (the honest direction)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- certifies a complete device readback (the honest direction)
- Every conjunct satisfied: device source, positive handle, positive identity, exact size
   - Expected: full.source equals `device_readback`
   - Expected: full.backend_handle equals `3`
   - Expected: full.device_identity equals `5`
   - Expected: full.pixel_count equals `(W * H).to_i64()`
   - Expected: web_gpu_readback_device_proven_for_frame(full, W, H) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("certifies a complete device readback (the honest direction)")
step("Every conjunct satisfied: device source, positive handle, positive identity, exact size")
val full = engine2d_readback_with_identity(_device_readback(), "device_readback", 3, 5)
expect(full.source).to_equal("device_readback")
expect(full.backend_handle).to_equal(3)
expect(full.device_identity).to_equal(5)
expect(full.pixel_count).to_equal((W * H).to_i64())
expect(web_gpu_readback_device_proven_for_frame(full, W, H)).to_equal(true)
```

</details>

#### rejects a readback that is not sourced from a device (source conjunct)

- rejects a readback that is not sourced from a device (source conjunct)
- A CPU fallback of exactly the right size is still not device-proven
   - Expected: web_gpu_readback_device_proven_for_frame(fallback, W, H) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a readback that is not sourced from a device (source conjunct)")
step("A CPU fallback of exactly the right size is still not device-proven")
val fallback = engine2d_readback_with_identity(_device_readback(), "cpu_fallback", 3, 5)
expect(web_gpu_readback_device_proven_for_frame(fallback, W, H)).to_equal(false)
```

</details>

#### rejects a readback with no backend handle (handle conjunct)

- rejects a readback with no backend handle (handle conjunct)
- handle == 0 means no backend owned the frame
   - Expected: web_gpu_readback_device_proven_for_frame(no_handle, W, H) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a readback with no backend handle (handle conjunct)")
step("handle == 0 means no backend owned the frame")
val no_handle = engine2d_readback_with_identity(_device_readback(), "device_readback", 0, 5)
expect(web_gpu_readback_device_proven_for_frame(no_handle, W, H)).to_equal(false)
```

</details>

#### rejects a readback with no device identity (identity conjunct)

- rejects a readback with no device identity (identity conjunct)
- identity == 0 means no device identified itself
   - Expected: web_gpu_readback_device_proven_for_frame(no_identity, W, H) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a readback with no device identity (identity conjunct)")
step("identity == 0 means no device identified itself")
val no_identity = engine2d_readback_with_identity(_device_readback(), "device_readback", 3, 0)
expect(web_gpu_readback_device_proven_for_frame(no_identity, W, H)).to_equal(false)
```

</details>

#### rejects a TRUNCATED device readback (pixel_count conjunct - the anti-truncation arm)

- rejects a TRUNCATED device readback (pixel_count conjunct - the anti-truncation arm)
- One pixel short of the frame, device-shaped in every other respect
   - Expected: short_rb.pixel_count equals `(W * H - 1).to_i64()`
   - Expected: web_gpu_readback_device_proven_for_frame(short_rb, W, H) is false
- A drastically truncated buffer is likewise refused, never partially credited
   - Expected: web_gpu_readback_device_proven_for_frame(tiny, W, H) is false
- An OVERSIZED readback is refused too - the conjunct is equality, not a floor
   - Expected: web_gpu_readback_device_proven_for_frame(over, W, H) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a TRUNCATED device readback (pixel_count conjunct - the anti-truncation arm)")
step("One pixel short of the frame, device-shaped in every other respect")
val short_rb = engine2d_readback_with_identity(_pixels(W * H - 1), "device_readback", 3, 5)
expect(short_rb.pixel_count).to_equal((W * H - 1).to_i64())
expect(web_gpu_readback_device_proven_for_frame(short_rb, W, H)).to_equal(false)
step("A drastically truncated buffer is likewise refused, never partially credited")
val tiny = engine2d_readback_with_identity(_pixels(1), "device_readback", 3, 5)
expect(web_gpu_readback_device_proven_for_frame(tiny, W, H)).to_equal(false)
step("An OVERSIZED readback is refused too - the conjunct is equality, not a floor")
val over = engine2d_readback_with_identity(_pixels(W * H + 1), "device_readback", 3, 5)
expect(web_gpu_readback_device_proven_for_frame(over, W, H)).to_equal(false)
```

</details>

#### compares the pixel count at i64 width (tripwire: NON-BITING on this engine, see docstring)

- compares the pixel count at i64 width (tripwire: NON-BITING on this engine, see docstring)
- Record the measured premise: a value declared i32 does not wrap at 32 bits here
   - Expected: (ow * oh).to_i64() equals `4295229440`
- So the wrapped value 262144 is NOT what the predicate compares against
   - Expected: web_gpu_readback_device_proven_for_frame(wrapped, ow, oh) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compares the pixel count at i64 width (tripwire: NON-BITING on this engine, see docstring)")
step("Record the measured premise: a value declared i32 does not wrap at 32 bits here")
val ow: i32 = 65540
val oh: i32 = 65536
expect((ow * oh).to_i64()).to_equal(4295229440)
step("So the wrapped value 262144 is NOT what the predicate compares against")
val wrapped = engine2d_readback_with_identity(_pixels(262144), "device_readback", 7, 9)
expect(web_gpu_readback_device_proven_for_frame(wrapped, ow, oh)).to_equal(false)
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

- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fe4cbfe46919f3d7f2be255ca1bed4a56a746220c7ef75a079b0ae569baa07b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fe4cbfe46919f3d7f2be255ca1bed4a56a746220c7ef75a079b0ae569baa07b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fe4cbfe46919f3d7f2be255ca1bed4a56a746220c7ef75a079b0ae569baa07b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'certifies a complete device readback (the honest direction)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a readback that is not sourced from a device (source conjunct)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_provenance_predicate_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a readback with no backend handle (handle conjunct)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
