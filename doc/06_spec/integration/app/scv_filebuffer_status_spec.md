# scv_filebuffer_status_spec

> Purpose: Proves the SCV one-read FileBuffer (SCV-MIG-19, scv_v2_final_report

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_filebuffer_status_spec

Purpose: Proves the SCV one-read FileBuffer (SCV-MIG-19, scv_v2_final_report

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_filebuffer_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Proves the SCV one-read FileBuffer (SCV-MIG-19, scv_v2_final_report
§6.5): a snapshot reads each changed file exactly once, and everything —
content id, chunk-store write, CDC chunk map, file object — derives from that
single buffer. Byte-compat is critical: buffer-path ids must equal the legacy
read-per-derivation path's ids, so existing repositories' hashes never change.
Single-read is proven by clobbering the on-disk file AFTER the buffer read and
showing the written objects still carry the ORIGINAL content. Oversize files
are rejected against SCV_MAX_* bounds before allocation.
Audience: Maintainers of the SCV storage layer.

## Scenarios

### SCV one-read FileBuffer

#### matches the legacy multi-read path byte-for-byte (small file)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the legacy multi-read path byte-for-byte (small file)
   - Expected: buffer.error equals ``
   - Expected: buffer.size equals `10`
   - Expected: buf_chunk equals `legacy_chunk`
   - Expected: buf_file equals `legacy_file`
   - Expected: scv_file_buffer_content_id(buffer) equals `legacy_chunk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the legacy multi-read path byte-for-byte (small file)")
val root_a = _new_root()
val root_b = _new_root()
val path_a = "{root_a}/a.txt"
val path_b = "{root_b}/a.txt"
_write_file(path_a, "printf 'hello scv\\n'")
_write_file(path_b, "printf 'hello scv\\n'")
# legacy path: separate reads for content id, chunk copy, file object
val legacy_chunk = scv_write_chunk_from_file(root_a, path_a)
val legacy_file = scv_write_file_object(root_a, "a.txt", legacy_chunk, 10, 42)
# buffer path: one read
val buffer = scv_file_buffer_read(path_b)
expect(buffer.error).to_equal("")
expect(buffer.size).to_equal(10)
val (buf_file, buf_chunk) = scv_file_buffer_write_objects(root_b, "a.txt", buffer, 42)
expect(buf_chunk).to_equal(legacy_chunk)
expect(buf_file).to_equal(legacy_file)
expect(scv_file_buffer_content_id(buffer)).to_equal(legacy_chunk)
```

</details>

#### matches the legacy path on a CDC-chunked file (> chunk min size)

- matches the legacy path on a CDC-chunked file (> chunk min size)
   - Expected: buffer.error equals ``
   - Expected: buffer.size equals `size_a`
   - Expected: buf_chunk equals `legacy_chunk`
   - Expected: buf_file equals `legacy_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the legacy path on a CDC-chunked file (> chunk min size)")
val root_a = _new_root()
val root_b = _new_root()
val path_a = "{root_a}/big.bin"
val path_b = "{root_b}/big.bin"
_write_file(path_a, "seq 1 1500 | tr '\\n' 'x'")
_write_file(path_b, "seq 1 1500 | tr '\\n' 'x'")
val size_a = scv_file_buffer_read(path_a).size
val legacy_chunk = scv_write_chunk_from_file(root_a, path_a)
val legacy_file = scv_write_file_object(root_a, "big.bin", legacy_chunk, size_a, 42)
val buffer = scv_file_buffer_read(path_b)
expect(buffer.error).to_equal("")
expect(buffer.size).to_equal(size_a)
val (buf_file, buf_chunk) = scv_file_buffer_write_objects(root_b, "big.bin", buffer, 42)
expect(buf_chunk).to_equal(legacy_chunk)
expect(buf_file).to_equal(legacy_file)
```

</details>

#### reads exactly once: clobbering the file after buffering changes nothing

- reads exactly once: clobbering the file after buffering changes nothing
   - Expected: buffer.error equals ``
   - Expected: chunk equals `original_id`
   - Expected: chunk == scv_content_id_for_file(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads exactly once: clobbering the file after buffering changes nothing")
val root = _new_root()
val path = "{root}/once.txt"
_write_file(path, "printf 'original content\\n'")
val buffer = scv_file_buffer_read(path)
expect(buffer.error).to_equal("")
val original_id = scv_file_buffer_content_id(buffer)
# clobber the on-disk file — if any derivation re-read the disk, the
# written chunk id would follow the new content
_write_file(path, "printf 'CLOBBERED after buffer read\\n'")
val (_file_id, chunk) = scv_file_buffer_write_objects(root, "once.txt", buffer, 42)
expect(chunk).to_equal(original_id)
expect(chunk == scv_content_id_for_file(path)).to_equal(false)
```

</details>

#### rejects an oversize file before reading it

- rejects an oversize file before reading it
   - Expected: buffer.error contains `over bound`
   - Expected: buffer.bytes.len() equals `0`
   - Expected: ok.error equals ``
   - Expected: ok.size equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an oversize file before reading it")
val root = _new_root()
val path = "{root}/big.txt"
_write_file(path, "printf '0123456789'")
val buffer = scv_file_buffer_read_bounded(path, 4)
expect(buffer.error.contains("over bound")).to_equal(true)
expect(buffer.bytes.len()).to_equal(0)
# in-bound read succeeds through the same entry point
val ok = scv_file_buffer_read_bounded(path, 10)
expect(ok.error).to_equal("")
expect(ok.size).to_equal(10)
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-FILEBUFFER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d52ac97072231d3269ac8a92fb472182d291a05e2c1bee6e0e8ddc6ad71c722`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d52ac97072231d3269ac8a92fb472182d291a05e2c1bee6e0e8ddc6ad71c722`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d52ac97072231d3269ac8a92fb472182d291a05e2c1bee6e0e8ddc6ad71c722`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_filebuffer_status_spec.spl
mirror: doc/06_spec/integration/app/scv_filebuffer_status_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/app/scv_filebuffer_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_filebuffer_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_filebuffer_status_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_filebuffer_status_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_filebuffer_status_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the legacy multi-read path byte-for-byte (small file)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_filebuffer_status_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the legacy path on a CDC-chunked file (> chunk min size)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_filebuffer_status_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads exactly once: clobbering the file after buffering changes nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
