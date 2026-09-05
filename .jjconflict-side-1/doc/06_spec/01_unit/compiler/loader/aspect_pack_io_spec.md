# Aspect Pack Io Specification

> Tests covering aspect pack I/O policy (design §15), AspectPackIndexCache (design §14.1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect Pack Io Specification

## Scenarios

### aspect pack I/O policy (design §15)

#### reads an UNALIGNED range byte-identically to the whole file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### records a nonzero intra-page delta and covers the range

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = pack_window_map(RAW_PATH, 4101, 100)
assert_true(w.ok, "unaligned window mapped: {w.error_code}")
assert_true(w.data_offset > 0, "unaligned request records an intra-page delta")
assert_true(w.address > 0, "window has a real mapping base")
assert_true(w.map_length >= w.data_offset + w.want_length, "aligned map covers the requested range")
assert_eq(pack_window_bytes(w).len(), 100, "window yields exactly the requested bytes")
# §15: no readahead of any kind is issued by the map itself.
assert_true(pack_window_unmap(w), "window unmapped")
```

</details>

#### reads the fixed trailer without knowing the layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val whole = file_read_bytes(RAW_PATH)
val tail = pack_read_trailer(RAW_PATH, 16)
assert_eq(tail.len(), 16, "trailer read returned the requested size")
var i = 0
var mismatches = 0
while i < 16:
    if tail[i] != whole[whole.len() - 16 + i]:
        mismatches = mismatches + 1
    i = i + 1
assert_eq(mismatches, 0, "trailer bytes match the end of the file")
file_delete(RAW_PATH)
```

</details>

### AspectPackIndexCache (design §14.1)

#### reads header+directory only, never the payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_write_pack()
val fsize = pack_file_size(PACK_PATH)
assert_true(fsize > 0, "pack fixture written")
val c = pack_index_cache_new()
val e = pack_index_get(c, PACK_PATH)
assert_true(e.ok, "index read succeeded: {e.error_code} {e.error_message}")
assert_eq(e.module_count, 2, "directory reports the two fixture modules")
assert_eq(e.file_size, fsize, "entry records the real file size")
assert_eq(e.index_bytes.len(), 32 + e.dir_size, "cached bytes are exactly header+directory")
assert_true(c.index_bytes_read > 0, "the index read actually happened ({c.index_bytes_read} bytes) -- a zero here makes the next assertion vacuous")
assert_true(c.index_bytes_read < fsize, "index read {c.index_bytes_read} bytes of a {fsize}-byte pack -- payload untouched")
assert_eq(c.payload_bytes_read, 0, "no payload byte was read")
```

</details>

#### serves a second lookup from cache without re-reading

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = pack_index_cache_new()
val first = pack_index_get(c, PACK_PATH)
assert_true(first.ok, "first lookup ok: {first.error_code}")
val after_first = c.index_bytes_read
val second = pack_index_get(c, PACK_PATH)
assert_true(second.ok, "second lookup ok")
assert_eq(c.hits, 1, "second lookup was a cache hit")
assert_eq(c.misses, 1, "only the first lookup missed")
assert_eq(c.index_bytes_read, after_first, "a cache hit reads no further bytes")
```

</details>

#### invalidates and evicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = pack_index_cache_new()
_ = pack_index_get(c, PACK_PATH)
assert_true(pack_index_invalidate(c, PACK_PATH), "invalidate removed the live entry")
assert_true(not pack_index_invalidate(c, PACK_PATH), "invalidate of an absent entry reports false")
_ = pack_index_get(c, PACK_PATH)
assert_eq(pack_index_evict_all(c), 1, "evict_all reports the number dropped")
file_delete(PACK_PATH)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/aspect_pack_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aspect pack I/O policy (design §15), AspectPackIndexCache (design §14.1).
- aspect pack I/O policy (design §15)
- AspectPackIndexCache (design §14.1)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `f20d6fe9daf109a7428ea34168e452514d1064c3e46358f2a8f2a947a0ad477a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f20d6fe9daf109a7428ea34168e452514d1064c3e46358f2a8f2a947a0ad477a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f20d6fe9daf109a7428ea34168e452514d1064c3e46358f2a8f2a947a0ad477a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/loader/aspect_pack_io_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/aspect_pack_io_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/aspect_pack_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/aspect_pack_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/aspect_pack_io_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/loader/aspect_pack_io_spec.spl:74:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads an UNALIGNED range byte-identically to the whole file' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/loader/aspect_pack_io_spec.spl:95:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records a nonzero intra-page delta and covers the range' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/loader/aspect_pack_io_spec.spl:106:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads the fixed trailer without knowing the layout' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/loader/aspect_pack_io_spec.spl:123:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reads header+directory only, never the payload' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
