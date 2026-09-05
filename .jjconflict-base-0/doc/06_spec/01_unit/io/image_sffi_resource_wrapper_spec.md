# image_sffi_resource_wrapper_spec

> Resource wrapper for Image — WP-J acceptance

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# image_sffi_resource_wrapper_spec

Resource wrapper for Image — WP-J acceptance

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/01_unit/io/image_sffi_resource_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Resource wrapper for Image — WP-J acceptance

Tests the new Image wrapper class with resource ownership pattern:
- Sentinel-based validity checks
- Consuming close() method
- Double-close guard (one-shot safety)
- Backward compatibility with deprecated ImageData aliases

## Scenarios

### Image resource wrapper

#### Image.is_valid checks sentinel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Image.is_valid checks sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Image.is_valid checks sentinel")
val img = Image(handle: 42, width: 100, height: 100, channels: 4)
assert_true(img.is_valid())
```

</details>

#### Image.is_valid detects invalid sentinel (0)

- Image.is_valid detects invalid sentinel (0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Image.is_valid detects invalid sentinel (0)")
val img = Image(handle: 0, width: 100, height: 100, channels: 4)
assert_false(img.is_valid())
```

</details>

#### Image sentinel is 0 not -1

- Image sentinel is 0 not -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Image sentinel is 0 not -1")
val img_zero = Image(handle: 0, width: 100, height: 100, channels: 4)
assert_false(img_zero.is_valid())
val img_neg = Image(handle: -1, width: 100, height: 100, channels: 4)
assert_true(img_neg.is_valid())
```

</details>

#### close on invalid handle is safe

- close on invalid handle is safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close on invalid handle is safe")
val img = Image(handle: 0, width: 100, height: 100, channels: 4)
img.close()
assert_equal(img.handle, 0)
img.close()
assert_equal(img.handle, 0)
```

</details>

#### pixel_count calculates correctly

- pixel_count calculates correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pixel_count calculates correctly")
val img = Image(handle: 42, width: 10, height: 20, channels: 4)
assert_equal(img.pixel_count(), 200)
```

</details>

#### size_bytes accounts for channels

- size_bytes accounts for channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("size_bytes accounts for channels")
val img = Image(handle: 42, width: 10, height: 20, channels: 4)
assert_equal(img.size_bytes(), 800)
```

</details>

#### get_pixel returns 0 for invalid handle

- get_pixel returns 0 for invalid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_pixel returns 0 for invalid handle")
val img = Image(handle: 0, width: 10, height: 20, channels: 4)
assert_equal(img.get_pixel(5, 5), 0)
```

</details>

#### ImageData (deprecated) still exists

- ImageData (deprecated) still exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ImageData (deprecated) still exists")
val img = ImageData(handle: 42, width: 100, height: 100, channels: 4)
assert_true(img.is_valid())
```

</details>

#### load_image (deprecated) still works

- load_image (deprecated) still works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("load_image (deprecated) still works")
val result = load_image("/nonexistent/path")
assert_nil(result)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `5929a9654eccd07aeef5d969eaee883324fd23e33daf57e7361034429391e280`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5929a9654eccd07aeef5d969eaee883324fd23e33daf57e7361034429391e280`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5929a9654eccd07aeef5d969eaee883324fd23e33daf57e7361034429391e280`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/io/image_sffi_resource_wrapper_spec.spl
mirror: doc/06_spec/01_unit/io/image_sffi_resource_wrapper_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/io/image_sffi_resource_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/io/image_sffi_resource_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/io/image_sffi_resource_wrapper_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Image.is_valid checks sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/image_sffi_resource_wrapper_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Image.is_valid detects invalid sentinel (0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/image_sffi_resource_wrapper_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Image sentinel is 0 not -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
