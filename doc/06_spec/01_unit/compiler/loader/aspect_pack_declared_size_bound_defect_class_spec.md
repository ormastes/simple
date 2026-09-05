# Aspect Pack Declared Size Bound Defect Class Specification

> Tests covering aspect-pack declared-size bound (defect class: trusting a declared size).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect Pack Declared Size Bound Defect Class Specification

## Scenarios

### aspect-pack declared-size bound (defect class: trusting a declared size)

#### refuses an over-declared directory size on the DECLARATION

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### refuses an over-declared range length on the DECLARATION

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _write("small", _build_bytes())
val w = pack_window_map(path, 0, APKIO_MAX_RANGE_BYTES + 1)
assert_true(not w.ok, "an over-declared range is refused")
assert_eq(w.error_code, "APKIO_RANGE_TOO_LARGE",
    "refused BY THE CAP -- if this reads APKIO_RANGE_PAST_EOF the range bound was removed")
assert_eq(w.address, 0, "nothing was mapped")
file_delete(path)
```

</details>

#### still refuses a within-cap range that runs past end of file

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The cap is not a substitute for the EOF check: a SHORT map would hand
# back the wrong bytes silently.
val path = _write("eof", _build_bytes())
val w = pack_window_map(path, 0, 1048576)
assert_true(not w.ok, "a range past EOF is refused")
assert_eq(w.error_code, "APKIO_RANGE_PAST_EOF", "refused by the end-of-file bound")
assert_eq(pack_read_range(path, 0, 1048576).len(), 0, "and yields no bytes")
file_delete(path)
```

</details>

#### refuses a declared total_size that disagrees with the file

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = _build_bytes()
_patch_u64(bytes, 24, bytes.len() + 512)   # total_size at offset 24
val path = _write("bad_total", bytes)
val c = pack_index_cache_new()
val e = pack_index_get(c, path)
assert_true(not e.ok, "a truncated pack is refused")
assert_eq(e.error_code, "APKIDX_TRUNCATED_PACK", "declared total_size is checked against the real file size")
file_delete(path)
```

</details>

#### refuses zero and negative declared directory sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = _build_bytes()
_patch_u64(bytes, 16, 0)
val path = _write("zero_dir", bytes)
val c = pack_index_cache_new()
val e = pack_index_get(c, path)
assert_true(not e.ok, "a zero-sized directory is refused")
assert_eq(e.error_code, "APKIDX_DIRECTORY_TOO_LARGE", "the same bound rejects a nonsensical low declaration")
file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aspect-pack declared-size bound (defect class: trusting a declared size).
- aspect-pack declared-size bound (defect class: trusting a declared size)

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

- Canonical SPipe generation for source `908eb0185744cf121fd4d7bd14ade54ce0f1b950d145da886e0f4245f24c2975`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `908eb0185744cf121fd4d7bd14ade54ce0f1b950d145da886e0f4245f24c2975`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `908eb0185744cf121fd4d7bd14ade54ce0f1b950d145da886e0f4245f24c2975`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl:67:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'refuses an over-declared directory size on the DECLARATION' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl:86:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'refuses an over-declared range length on the DECLARATION' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl:96:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still refuses a within-cap range that runs past end of file' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl:107:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'refuses a declared total_size that disagrees with the file' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
