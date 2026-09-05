# Exec Memory Bulk Write Specification

> Tests covering bulk exec-memory write.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exec Memory Bulk Write Specification

## Scenarios

### bulk exec-memory write

#### writes every byte of a page-sized section, not just the first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes every byte of a page-sized section, not just the first


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes every byte of a page-sized section, not just the first")
val size = 4096i64
val addr = native_alloc_rw_memory(size)
assert_true(addr != 0)
val code = ramp(size)
assert_eq(native_write_exec_memory(addr, code, 0), size)
val got = native_mmap_read_bytes(addr, 0, size)
assert_eq(got.len(), size)
# Sample the whole span, including the last byte -- a truncated copy
# that only wrote the head would still pass a first-byte-only check.
assert_eq(got[0] as i64, 0)
assert_eq(got[1] as i64, 1)
assert_eq(got[255] as i64, 255)
assert_eq(got[256] as i64, 0)
assert_eq(got[2048] as i64, 0)
assert_eq(got[size - 1] as i64, (size - 1) & 0xFF)
assert_true(native_munmap(addr, size))
```

</details>

#### honours a non-zero destination offset and leaves the head untouched

- honours a non-zero destination offset and leaves the head untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("honours a non-zero destination offset and leaves the head untouched")
val addr = native_alloc_rw_memory(4096)
assert_true(addr != 0)
# Zero the head so an off-by-offset copy is visible.
assert_eq(native_write_exec_memory(addr, ramp(16), 0), 16)
val payload: [u8] = [0xAA, 0xBB, 0xCC, 0xDD]
assert_eq(native_write_exec_memory(addr, payload, 64), 4)
val head = native_mmap_read_bytes(addr, 0, 4)
assert_eq(head[0] as i64, 0)
assert_eq(head[3] as i64, 3)
val got = native_mmap_read_bytes(addr, 64, 4)
assert_eq(got[0] as i64, 0xAA)
assert_eq(got[1] as i64, 0xBB)
assert_eq(got[2] as i64, 0xCC)
assert_eq(got[3] as i64, 0xDD)
assert_true(native_munmap(addr, 4096))
```

</details>

#### rejects invalid arguments before dereferencing anything

- rejects invalid arguments before dereferencing anything


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid arguments before dereferencing anything")
assert_eq(native_write_exec_memory(0, ramp(4), 0), 0)
assert_eq(native_write_exec_memory(1, ramp(4), -1), 0)
val empty: [u8] = []
val addr = native_alloc_rw_memory(4096)
assert_true(addr != 0)
assert_eq(native_write_exec_memory(addr, empty, 0), 0)
assert_true(native_munmap(addr, 4096))
```

</details>

#### reproduces the size at which the old boxed path was pathological

- reproduces the size at which the old boxed path was pathological


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reproduces the size at which the old boxed path was pathological")
# 64 KiB was 10x slower through the `[u8]` extern than through the
# per-byte loop. Content must be exact at that size too.
val size = 65536i64
val addr = native_alloc_rw_memory(size)
assert_true(addr != 0)
assert_eq(native_write_exec_memory(addr, ramp(size), 0), size)
val tail = native_mmap_read_bytes(addr, size - 4, 4)
assert_eq(tail[0] as i64, (size - 4) & 0xFF)
assert_eq(tail[3] as i64, (size - 1) & 0xFF)
assert_true(native_munmap(addr, size))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/exec_memory_bulk_write_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bulk exec-memory write.
- bulk exec-memory write

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `d64da750373fdd6d0435ad30d2fb5601776372f95239c00e0dec62900f2421e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d64da750373fdd6d0435ad30d2fb5601776372f95239c00e0dec62900f2421e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d64da750373fdd6d0435ad30d2fb5601776372f95239c00e0dec62900f2421e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/loader/exec_memory_bulk_write_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/exec_memory_bulk_write_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/exec_memory_bulk_write_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/exec_memory_bulk_write_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/exec_memory_bulk_write_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes every byte of a page-sized section, not just the first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/exec_memory_bulk_write_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'honours a non-zero destination offset and leaves the head untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/exec_memory_bulk_write_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid arguments before dereferencing anything' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
