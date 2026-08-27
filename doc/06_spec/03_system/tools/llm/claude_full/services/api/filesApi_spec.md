# Claude Full Files API

> Purpose: should choose default API base URL in source order

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Files API

Purpose: should choose default API base URL in source order

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/filesApi.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should choose default API base URL in source order
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Files API

## Overview

This SSpec pins the Claude CLI `services/api/filesApi.ts` parity slice. It
checks deterministic behavior for default base URL selection, retry backoff,
download path normalization, download save results, upload non-retriable errors,
upload retry exhaustion, list pagination, and file spec parsing.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/filesApi.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Syntax

Modern SSpec `describe`, `it`, `step`, and concrete `expect` assertions only.

## Scenarios

### Claude full filesApi

#### should choose default API base URL in source order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should choose default API base URL in source order
- Verify: should choose default API base URL in source order
- Prefer ANTHROPIC_BASE_URL, then CLAUDE_CODE_API_BASE_URL, then public API
   - Expected: getDefaultApiBaseUrl("https://env.anthropic", "https://cc") equals `https://env.anthropic`
   - Expected: getDefaultApiBaseUrl("", "https://cc") equals `https://cc`
   - Expected: getDefaultApiBaseUrl("", "") equals `https://api.anthropic.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should choose default API base URL in source order")
step("Verify: should choose default API base URL in source order")
# @req: REQ-TOOLS-File-001
step("Prefer ANTHROPIC_BASE_URL, then CLAUDE_CODE_API_BASE_URL, then public API")
expect(getDefaultApiBaseUrl("https://env.anthropic", "https://cc")).to_equal("https://env.anthropic")
expect(getDefaultApiBaseUrl("", "https://cc")).to_equal("https://cc")
expect(getDefaultApiBaseUrl("", "")).to_equal("https://api.anthropic.com")
```

</details>

#### should retry with exponential backoff and final error

- should retry with exponential backoff and final error
- Verify: should retry with exponential backoff and final error
- Run three retryable failures
   - Expected: result.done is false
   - Expected: client.sleeps[0] equals `500`
   - Expected: client.sleeps[1] equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retry with exponential backoff and final error")
step("Verify: should retry with exponential backoff and final error")
# @req: REQ-TOOLS-File-001
step("Run three retryable failures")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
val result = client.retryWithBackoff("Download file file_a", [RetryResult.again("e1"), RetryResult.again("e2"), RetryResult.again("e3")])
expect(result.done).to_equal(false)
expect(result.error).to_contain("after 3 attempts")
expect(client.sleeps[0]).to_equal(500)  # oracle: value fixed by the spec contract
expect(client.sleeps[1]).to_equal(1000)  # oracle: value fixed by the spec contract
```

</details>

#### should build safe download paths and reject traversal

- should build safe download paths and reject traversal
- Verify: should build safe download paths and reject traversal
- Strip redundant upload prefixes
   - Expected: client.buildDownloadPath("sess", "/uploads/dir/a.txt") equals `/repo/sess/uploads/dir/a.txt`
   - Expected: client.buildDownloadPath("sess", "../secret") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build safe download paths and reject traversal")
step("Verify: should build safe download paths and reject traversal")
# @req: REQ-TOOLS-File-001
step("Strip redundant upload prefixes")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.cwd = "/repo"
expect(client.buildDownloadPath("sess", "/uploads/dir/a.txt")).to_equal("/repo/sess/uploads/dir/a.txt")
expect(client.buildDownloadPath("sess", "../secret")).to_equal("")
expect(client.debug[0]).to_contain("Path must not traverse")
```

</details>

#### should download and save successful files

- should download and save successful files
- Verify: should download and save successful files
- Plan a 200 download response
   - Expected: result.success is true
   - Expected: result.bytesWritten equals `12`
   - Expected: client.mkdirs[0] equals `/workspace/sess/uploads/dir`
   - Expected: client.writes[0] equals `/workspace/sess/uploads/dir/a.txt:12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should download and save successful files")
step("Verify: should download and save successful files")
# @req: REQ-TOOLS-File-001
step("Plan a 200 download response")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.downloadPlan = [FilesApiResponse.okFile(12)]
val result = client.downloadAndSaveFile(File.new("file_1", "dir/a.txt"))
expect(result.success).to_equal(true)
expect(result.bytesWritten).to_equal(12)  # oracle: value fixed by the spec contract
expect(client.mkdirs[0]).to_equal("/workspace/sess/uploads/dir")
expect(client.writes[0]).to_equal("/workspace/sess/uploads/dir/a.txt:12")
```

</details>

#### should return non-retriable upload failures without network analytics

- should return non-retriable upload failures without network analytics
- Verify: should return non-retriable upload failures without network analytics
- Plan an upload 401
   - Expected: result.success is false
   - Expected: client.analytics[0] equals `tengu_file_upload_failed:auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return non-retriable upload failures without network analytics")
step("Verify: should return non-retriable upload failures without network analytics")
# @req: REQ-TOOLS-File-001
step("Plan an upload 401")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.readPlan = [FilesApiResponse.okFile(10)]
client.uploadPlan = [FilesApiResponse.status(401)]
val result = client.uploadFile("/tmp/a.txt", "a.txt")
expect(result.success).to_equal(false)
expect(result.error).to_contain("Authentication failed")
expect(client.analytics[0]).to_equal("tengu_file_upload_failed:auth")
```

</details>

#### should retry upload network failures and log network exhaustion

- should retry upload network failures and log network exhaustion
- Verify: should retry upload network failures and log network exhaustion
- Plan three retryable upload failures
   - Expected: result.success is false
   - Expected: client.analytics[0] equals `tengu_file_upload_failed:network`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retry upload network failures and log network exhaustion")
step("Verify: should retry upload network failures and log network exhaustion")
# @req: REQ-TOOLS-File-001
step("Plan three retryable upload failures")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.readPlan = [FilesApiResponse.okFile(10)]
client.uploadPlan = [FilesApiResponse.network("net1"), FilesApiResponse.network("net2"), FilesApiResponse.network("net3")]
val result = client.uploadFile("/tmp/a.txt", "a.txt")
expect(result.success).to_equal(false)
expect(result.error).to_contain("after 3 attempts")
expect(client.analytics[0]).to_equal("tengu_file_upload_failed:network")
```

</details>

#### should upload session files in input order

- should upload session files in input order
- Verify: should upload session files in input order
- Plan two successful uploads
   - Expected: results.len() equals `2`
   - Expected: results[0].fileId equals `file_a`
   - Expected: results[1].fileId equals `file_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should upload session files in input order")
step("Verify: should upload session files in input order")
# @req: REQ-TOOLS-File-001
step("Plan two successful uploads")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.readPlan = [FilesApiResponse.okFile(3), FilesApiResponse.okFile(4)]
client.uploadPlan = [FilesApiResponse.okUpload(201, "file_a"), FilesApiResponse.okUpload(200, "file_b")]
val results = client.uploadSessionFiles([LocalUploadFile.new("/a", "a.txt"), LocalUploadFile.new("/b", "b.txt")], 5)
expect(results.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(results[0].fileId).to_equal("file_a")
expect(results[1].fileId).to_equal("file_b")
```

</details>

#### should paginate file listing with after_id cursor

- should paginate file listing with after_id cursor
- Verify: should paginate file listing with after_id cursor
- Plan two list pages
   - Expected: files.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should paginate file listing with after_id cursor")
step("Verify: should paginate file listing with after_id cursor")
# @req: REQ-TOOLS-File-001
step("Plan two list pages")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.listPlan = [
    FilesApiPage.new([FileMetadata.new("a.txt", "file_a", 3)], true),
    FilesApiPage.new([FileMetadata.new("b.txt", "file_b", 4)], false),
]
val files = client.listFilesCreatedAfter("2026-01-01T00:00:00Z")
expect(files.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(client.requests[1]).to_contain("after_id=file_a")
```

</details>

#### should parse colon specs and expand gateway space-separated input

- should parse colon specs and expand gateway space-separated input
- Verify: should parse colon specs and expand gateway space-separated input
- Parse mixed file spec strings
   - Expected: files.len() equals `2`
   - Expected: files[0].fileId equals `file_a`
   - Expected: files[1].relativePath equals `dir/b.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse colon specs and expand gateway space-separated input")
step("Verify: should parse colon specs and expand gateway space-separated input")
# @req: REQ-TOOLS-File-001
step("Parse mixed file spec strings")
val files = parseFileSpecs(["file_a:a.txt file_b:dir/b.txt", "bad", ":missing", "file_c:"])
expect(files.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(files[0].fileId).to_equal("file_a")
expect(files[1].relativePath).to_equal("dir/b.txt")
```

</details>

#### should expose source-backed constants and error class

- should expose source-backed constants and error class
- Verify: should expose source-backed constants and error class
- Pin constants and class target
   - Expected: error.name equals `UploadNonRetriableError`
   - Expected: error.message equals `Upload canceled`
   - Expected: filesApiBetaHeader() equals `files-api-2025-04-14,oauth-2025-04-20`
   - Expected: filesApiSourceLinesModeled() equals `748`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed constants and error class")
step("Verify: should expose source-backed constants and error class")
# @req: REQ-TOOLS-File-001
step("Pin constants and class target")
val error = UploadNonRetriableError.new("Upload canceled")
expect(error.name).to_equal("UploadNonRetriableError")
expect(error.message).to_equal("Upload canceled")
expect(filesApiBetaHeader()).to_equal("files-api-2025-04-14,oauth-2025-04-20")
expect(filesApiSourceLinesModeled()).to_equal(748)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `N/A - strict llm_caret Claude CLI parity lane.`
- **Plan:** `N/A - target selected from strict checker output.`
- **Design:** `N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/filesApi.ts`.`
- **Research:** `N/A - upstream TypeScript file is the source reference.`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-File-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a28596bce2a471466708b6e1ccc053bf23c8b40c9c545590082d6494633c6e49`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a28596bce2a471466708b6e1ccc053bf23c8b40c9c545590082d6494633c6e49`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a28596bce2a471466708b6e1ccc053bf23c8b40c9c545590082d6494633c6e49`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/api/filesApi_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/api/filesApi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/api/filesApi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should choose default API base URL in source order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should choose default API base URL in source order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retry with exponential backoff and final error' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retry with exponential backoff and final error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build safe download paths and reject traversal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build safe download paths and reject traversal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should download and save successful files' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return non-retriable upload failures without network analytics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/api/filesApi_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retry upload network failures and log network exhaustion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
