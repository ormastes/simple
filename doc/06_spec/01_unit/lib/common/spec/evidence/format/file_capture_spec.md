# Real-file capture format adapter

> This spec reads REAL files from disk that this spec run itself writes into

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Real-file capture format adapter

This spec reads REAL files from disk that this spec run itself writes into

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/evidence/format/file_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

This spec reads REAL files from disk that this spec run itself writes into
the scratchpad directory during execution — the fixtures are not string
literals typed into the spec, they are actual bytes actually written by
`std.nogc_sync_mut.io_runtime.file_write` and actually read back by
`file_capture.capture_file` / `file_capture.file_json_to_evidence` through
real `file_exists`/`file_size`/`file_read` calls against the real
filesystem. A reader should come away convinced the exists/size/hash values
below describe files that really existed (or really didn't) on disk during
this run, not fixtures that merely happen to exist.

## Scenarios

### Real-file capture format adapter

#### captures a nonexistent path as a real failure, never a silently-valid empty file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures a nonexistent path as a real failure, never a silently-valid empty file
- Point capture_file at a path that has never been written
   - Expected: file_exists(missing_path) is false
- Verify the capture records a real absence, not an empty-but-valid file
   - Expected: capture.exists is false
   - Expected: capture.size_bytes equals `0`
   - Expected: capture.sha256 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("captures a nonexistent path as a real failure, never a silently-valid empty file")
step("Point capture_file at a path that has never been written")
val missing_path = SCRATCH_DIR + "/file_capture_never_written_xyz123.txt"
file_delete(missing_path)
expect(file_exists(missing_path)).to_equal(false)

step("Verify the capture records a real absence, not an empty-but-valid file")
val capture = capture_file(missing_path)
expect(capture.exists).to_equal(false)
expect(capture.size_bytes).to_equal(0)
expect(capture.sha256).to_equal("")
```

</details>

#### records the ACTUAL byte count of a file this spec really wrote

- records the ACTUAL byte count of a file this spec really wrote
- Write a real file with a known, deliberately odd-length body
   - Expected: file_write(path, body) is true
- Capture it for real and verify size_bytes matches the real byte count, not a hardcoded number
   - Expected: capture.exists is true
   - Expected: capture.size_bytes equals `body.len()`
   - Expected: capture.size_bytes equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records the ACTUAL byte count of a file this spec really wrote")
step("Write a real file with a known, deliberately odd-length body")
val path = SCRATCH_DIR + "/file_capture_size_probe.txt"
val body = "0123456789abcde"
expect(file_write(path, body)).to_equal(true)

step("Capture it for real and verify size_bytes matches the real byte count, not a hardcoded number")
val capture = capture_file(path)
expect(capture.exists).to_equal(true)
expect(capture.size_bytes).to_equal(body.len())
expect(capture.size_bytes).to_equal(15)
```

</details>

#### recomputes the sha256 from ACTUAL bytes each capture, so two different files hash differently

- recomputes the sha256 from ACTUAL bytes each capture, so two different files hash differently
- Write real content A to a real path and capture it
   - Expected: file_write(path, "first-real-content-aaa") is true
   - Expected: capture_a.exists is true
   - Expected: capture_a.sha256.len() equals `64`
- Overwrite the SAME path with different real content and capture it again
   - Expected: file_write(path, "second-real-content-bbb-different") is true
   - Expected: capture_b.exists is true
   - Expected: capture_b.sha256.len() equals `64`
- Verify the two real captures produced two different hashes, proving live recomputation
   - Expected: capture_a.sha256 == capture_b.sha256 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("recomputes the sha256 from ACTUAL bytes each capture, so two different files hash differently")
step("Write real content A to a real path and capture it")
val path = SCRATCH_DIR + "/file_capture_hash_probe.txt"
expect(file_write(path, "first-real-content-aaa")).to_equal(true)
val capture_a = capture_file(path)
expect(capture_a.exists).to_equal(true)
expect(capture_a.sha256.len()).to_equal(64)

step("Overwrite the SAME path with different real content and capture it again")
expect(file_write(path, "second-real-content-bbb-different")).to_equal(true)
val capture_b = capture_file(path)
expect(capture_b.exists).to_equal(true)
expect(capture_b.sha256.len()).to_equal(64)

step("Verify the two real captures produced two different hashes, proving live recomputation")
expect(capture_a.sha256 == capture_b.sha256).to_equal(false)
```

</details>

#### builds typed evidence from a live file capture and verifies it end to end against a closed oracle

- builds typed evidence from a live file capture and verifies it end to end against a closed oracle
- Write a real probe file and capture it for real, right now
   - Expected: file_write(path, "evidence-probe-body") is true
   - Expected: capture.exists is true
- Convert the live capture into canonical evidence
   - Expected: evidence.parse_ok is true
- Verify the live-captured evidence against a closed oracle built from the real outcome
   - Expected: result.summary equals `4 check(s) passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds typed evidence from a live file capture and verifies it end to end against a closed oracle")
step("Write a real probe file and capture it for real, right now")
val path = SCRATCH_DIR + "/file_capture_evidence_probe.txt"
expect(file_write(path, "evidence-probe-body")).to_equal(true)
val capture = capture_file(path)
expect(capture.exists).to_equal(true)

step("Convert the live capture into canonical evidence")
val evidence = file_capture_to_evidence(capture, "file-probe/1")
expect(evidence.parse_ok).to_equal(true)

step("Verify the live-captured evidence against a closed oracle built from the real outcome")
val spec = oracle_spec_open(
    "file-probe/1",
    [
        check_exact("file-probe/1.path", path),
        check_exact("file-probe/1.exists", "true"),
        check_exact("file-probe/1.size_bytes", "{capture.size_bytes}"),
        check_exact("file-probe/1.sha256", capture.sha256)
    ]
)
val result = compare_evidence(evidence, spec)
expect(result.summary).to_equal("4 check(s) passed")
```

</details>

#### pipes a REAL JSON file's real bytes through the JSON evidence adapter for pointer-level oracles

- pipes a REAL JSON file's real bytes through the JSON evidence adapter for pointer-level oracles
- Write a real, well-formed JSON file to disk
   - Expected: file_write(path, "{\"status\": \"ok\", \"count\": 3}") is true
- Read it back through file_json_to_evidence, parsing the ACTUAL bytes on disk
   - Expected: evidence.parse_ok is true
- Verify a JSON-Pointer oracle resolves against the real parsed file content
   - Expected: result.summary equals `2 check(s) passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pipes a REAL JSON file's real bytes through the JSON evidence adapter for pointer-level oracles")
step("Write a real, well-formed JSON file to disk")
val path = SCRATCH_DIR + "/file_capture_json_probe.json"
expect(file_write(path, "{\"status\": \"ok\", \"count\": 3}")).to_equal(true)

step("Read it back through file_json_to_evidence, parsing the ACTUAL bytes on disk")
val evidence = file_json_to_evidence(path, "file-json-probe/1")
expect(evidence.parse_ok).to_equal(true)

step("Verify a JSON-Pointer oracle resolves against the real parsed file content")
val spec = oracle_spec_open(
    "file-json-probe/1",
    [
        check_exact("/status", "ok"),
        check_exact("/count", "3")
    ]
)
val result = compare_evidence(evidence, spec)
expect(result.summary).to_equal("2 check(s) passed")
```

</details>

#### returns a parse-error evidence for a REAL file containing malformed JSON, never a partial node set

- returns a parse-error evidence for a REAL file containing malformed JSON, never a partial node set
- Write a real file with deliberately malformed JSON content
   - Expected: file_write(path, "{\"status\": \"ok\", ") is true
- Parse the real malformed bytes and verify a parse-error result, not a partial success
   - Expected: evidence.parse_ok is false
   - Expected: evidence.nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a parse-error evidence for a REAL file containing malformed JSON, never a partial node set")
step("Write a real file with deliberately malformed JSON content")
val path = SCRATCH_DIR + "/file_capture_malformed_probe.json"
expect(file_write(path, "{\"status\": \"ok\", ")).to_equal(true)

step("Parse the real malformed bytes and verify a parse-error result, not a partial success")
val evidence = file_json_to_evidence(path, "file-json-probe/2")
expect(evidence.parse_ok).to_equal(false)
expect(evidence.nodes.len()).to_equal(0)
```

</details>

#### returns a parse-error evidence when the target path does not exist on disk

- returns a parse-error evidence when the target path does not exist on disk
- Point file_json_to_evidence at a path that has never been written
   - Expected: file_exists(missing_path) is false
- Verify a real absence is reported as a parse error, never an empty-but-valid document
   - Expected: evidence.parse_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a parse-error evidence when the target path does not exist on disk")
step("Point file_json_to_evidence at a path that has never been written")
val missing_path = SCRATCH_DIR + "/file_capture_json_never_written_xyz123.json"
file_delete(missing_path)
expect(file_exists(missing_path)).to_equal(false)

step("Verify a real absence is reported as a parse error, never an empty-but-valid document")
val evidence = file_json_to_evidence(missing_path, "file-json-probe/3")
expect(evidence.parse_ok).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5b941da8aea5634a9892289311b385043162055dcd4ff12f33da74c7f8a83116`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b941da8aea5634a9892289311b385043162055dcd4ff12f33da74c7f8a83116`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b941da8aea5634a9892289311b385043162055dcd4ff12f33da74c7f8a83116`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/common/spec/evidence/format/file_capture_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/evidence/format/file_capture_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/evidence/format/file_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/evidence/format/file_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/evidence/format/file_capture_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
