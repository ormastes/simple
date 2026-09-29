# dbfs_engine_pager_spec

> DBFS Pager Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_engine_pager_spec

DBFS Pager Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_engine_pager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Pager Specification

Verifies the single-cache pager used by DbFsEngine:
  1. alloc_page returns a fresh writable page
  2. read_page round-trips data written via write_page
  3. dirty tracking: written page is dirty; clean after flush
  4. page eviction under capacity stays correct
  5. single-cache discipline: no calls into kernel page cache

## Scenarios

### DBFS Pager — alloc and write

#### alloc_page returns a unique PageId

- alloc_page returns a unique PageId


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("alloc_page returns a unique PageId")
val p = DbfsPager.new(capacity: 16)
val id1 = p.alloc_page().unwrap()
val id2 = p.alloc_page().unwrap()
expect(id1).to_not_equal(id2)
```

</details>

#### write_page then read_page round-trips data

- write_page then read_page round-trips data
   - Expected: got.byte_at(0) equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write_page then read_page round-trips data")
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
val data = PageData.zeroed()
data.set_byte(0, 0xAB)
p.write_page(id, data).unwrap()
val got = p.read_page(id).unwrap()
expect(got.byte_at(0)).to_equal(0xAB)
```

</details>

#### page size constant is 8192 bytes

- page size constant is 8192 bytes
   - Expected: PAGE_SIZE_BYTES equals `8192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("page size constant is 8192 bytes")
expect(PAGE_SIZE_BYTES).to_equal(8192)
```

</details>

### DBFS Pager — dirty tracking
_Dirty/clean state transitions._

#### newly written page is dirty

- newly written page is dirty
   - Expected: p.is_dirty(id) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("newly written page is dirty")
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
p.write_page(id, PageData.zeroed()).unwrap()
expect(p.is_dirty(id)).to_equal(true)
```

</details>

#### page is clean after flush

- page is clean after flush
   - Expected: p.is_dirty(id) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("page is clean after flush")
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
p.write_page(id, PageData.zeroed()).unwrap()
p.flush_page(id).unwrap()
expect(p.is_dirty(id)).to_equal(false)
```

</details>

#### unflushed pages appear in dirty_pages list

- unflushed pages appear in dirty_pages list
   - Expected: dirty contains `id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unflushed pages appear in dirty_pages list")
val p = DbfsPager.new(capacity: 16)
val id = p.alloc_page().unwrap()
p.write_page(id, PageData.zeroed()).unwrap()
val dirty = p.dirty_pages()
expect(dirty.contains(id)).to_equal(true)
```

</details>

### DBFS Pager — eviction
_LRU eviction does not corrupt content._

#### evicted and re-read page returns correct data

- evicted and re-read page returns correct data
   - Expected: got.byte_at(0) equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("evicted and re-read page returns correct data")
val p = DbfsPager.new(capacity: 4)
val id = p.alloc_page().unwrap()
val data = PageData.zeroed()
data.set_byte(0, 0x42)
p.write_page(id, data).unwrap()
p.flush_page(id).unwrap()
# Fill cache to force eviction of our page
var i: i64 = 0
while i < 8:
    val tmp = p.alloc_page().unwrap()
    p.write_page(tmp, PageData.zeroed()).unwrap()
    p.flush_page(tmp).unwrap()
    i = i + 1
val got = p.read_page(id).unwrap()
expect(got.byte_at(0)).to_equal(0x42)
```

</details>

### DBFS Pager — single-cache discipline
_Pager must not expose a kernel-cache path._

#### pager has no kernel_cache_write method

- pager has no kernel_cache_write method
   - Expected: has_method is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pager has no kernel_cache_write method")
# Structural check: DbfsPager does not implement kernel_cache_write.
# Phase 5 must ensure the type does not expose this symbol.
val p = DbfsPager.new(capacity: 4)
val has_method = p.has_method("kernel_cache_write")
expect(has_method).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1fb910defbec4b131b21d1539aa15b90b2c767d55a85a9f9c71e973c3e442ba7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1fb910defbec4b131b21d1539aa15b90b2c767d55a85a9f9c71e973c3e442ba7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1fb910defbec4b131b21d1539aa15b90b2c767d55a85a9f9c71e973c3e442ba7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/storage/dbfs/dbfs_engine_pager_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_engine_pager_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_engine_pager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_engine_pager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_engine_pager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/dbfs_engine_pager_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'alloc_page returns a unique PageId' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_engine_pager_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'write_page then read_page round-trips data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_engine_pager_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'page size constant is 8192 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
