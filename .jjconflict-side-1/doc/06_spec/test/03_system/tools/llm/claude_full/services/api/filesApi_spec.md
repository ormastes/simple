# Claude Full Files API

> This SSpec pins the Claude CLI `services/api/filesApi.ts` parity slice. It checks deterministic behavior for default base URL selection, retry backoff, download path normalization, download save results, upload non-retriable errors, upload retry exhaustion, list pagination, and file spec parsing.

<!-- sdn-diagram:id=filesApi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=filesApi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

filesApi_spec -> std
filesApi_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=filesApi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Files API

This SSpec pins the Claude CLI `services/api/filesApi.ts` parity slice. It checks deterministic behavior for default base URL selection, retry backoff, download path normalization, download save results, upload non-retriable errors, upload retry exhaustion, list pagination, and file spec parsing.

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

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

- Prefer ANTHROPIC_BASE_URL, then CLAUDE_CODE_API_BASE_URL, then public API
   - Expected: getDefaultApiBaseUrl("https://env.anthropic", "https://cc") equals `https://env.anthropic`
   - Expected: getDefaultApiBaseUrl("", "https://cc") equals `https://cc`
   - Expected: getDefaultApiBaseUrl("", "") equals `https://api.anthropic.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prefer ANTHROPIC_BASE_URL, then CLAUDE_CODE_API_BASE_URL, then public API")
expect(getDefaultApiBaseUrl("https://env.anthropic", "https://cc")).to_equal("https://env.anthropic")
expect(getDefaultApiBaseUrl("", "https://cc")).to_equal("https://cc")
expect(getDefaultApiBaseUrl("", "")).to_equal("https://api.anthropic.com")
```

</details>

#### should retry with exponential backoff and final error

- Run three retryable failures
   - Expected: result.done is false
   - Expected: client.sleeps[0] equals `500`
   - Expected: client.sleeps[1] equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run three retryable failures")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
val result = client.retryWithBackoff("Download file file_a", [RetryResult.again("e1"), RetryResult.again("e2"), RetryResult.again("e3")])
expect(result.done).to_equal(false)
expect(result.error).to_contain("after 3 attempts")
expect(client.sleeps[0]).to_equal(500)
expect(client.sleeps[1]).to_equal(1000)
```

</details>

#### should build safe download paths and reject traversal

- Strip redundant upload prefixes
   - Expected: client.buildDownloadPath("sess", "/uploads/dir/a.txt") equals `/repo/sess/uploads/dir/a.txt`
   - Expected: client.buildDownloadPath("sess", "../secret") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Strip redundant upload prefixes")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.cwd = "/repo"
expect(client.buildDownloadPath("sess", "/uploads/dir/a.txt")).to_equal("/repo/sess/uploads/dir/a.txt")
expect(client.buildDownloadPath("sess", "../secret")).to_equal("")
expect(client.debug[0]).to_contain("Path must not traverse")
```

</details>

#### should download and save successful files

- Plan a 200 download response
- client downloadPlan = [FilesApiResponse okFile
   - Expected: result.success is true
   - Expected: result.bytesWritten equals `12`
   - Expected: client.mkdirs[0] equals `/workspace/sess/uploads/dir`
   - Expected: client.writes[0] equals `/workspace/sess/uploads/dir/a.txt:12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a 200 download response")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.downloadPlan = [FilesApiResponse.okFile(12)]
val result = client.downloadAndSaveFile(File.new("file_1", "dir/a.txt"))
expect(result.success).to_equal(true)
expect(result.bytesWritten).to_equal(12)
expect(client.mkdirs[0]).to_equal("/workspace/sess/uploads/dir")
expect(client.writes[0]).to_equal("/workspace/sess/uploads/dir/a.txt:12")
```

</details>

#### should return non-retriable upload failures without network analytics

- Plan an upload 401
- client readPlan = [FilesApiResponse okFile
- client uploadPlan = [FilesApiResponse status
   - Expected: result.success is false
   - Expected: client.analytics[0] equals `tengu_file_upload_failed:auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Plan three retryable upload failures
- client readPlan = [FilesApiResponse okFile
- client uploadPlan = [FilesApiResponse network
   - Expected: result.success is false
   - Expected: client.analytics[0] equals `tengu_file_upload_failed:network`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Plan two successful uploads
- client readPlan = [FilesApiResponse okFile
- client uploadPlan = [FilesApiResponse okUpload
   - Expected: results.len() equals `2`
   - Expected: results[0].fileId equals `file_a`
   - Expected: results[1].fileId equals `file_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan two successful uploads")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.readPlan = [FilesApiResponse.okFile(3), FilesApiResponse.okFile(4)]
client.uploadPlan = [FilesApiResponse.okUpload(201, "file_a"), FilesApiResponse.okUpload(200, "file_b")]
val results = client.uploadSessionFiles([LocalUploadFile.new("/a", "a.txt"), LocalUploadFile.new("/b", "b.txt")], 5)
expect(results.len()).to_equal(2)
expect(results[0].fileId).to_equal("file_a")
expect(results[1].fileId).to_equal("file_b")
```

</details>

#### should paginate file listing with after_id cursor

- Plan two list pages
- FilesApiPage new
- FilesApiPage new
   - Expected: files.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan two list pages")
val client = FilesApiClient.new(FilesApiConfig.new("tok", "sess"))
client.listPlan = [
    FilesApiPage.new([FileMetadata.new("a.txt", "file_a", 3)], true),
    FilesApiPage.new([FileMetadata.new("b.txt", "file_b", 4)], false),
]
val files = client.listFilesCreatedAfter("2026-01-01T00:00:00Z")
expect(files.len()).to_equal(2)
expect(client.requests[1]).to_contain("after_id=file_a")
```

</details>

#### should parse colon specs and expand gateway space-separated input

- Parse mixed file spec strings
   - Expected: files.len() equals `2`
   - Expected: files[0].fileId equals `file_a`
   - Expected: files[1].relativePath equals `dir/b.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse mixed file spec strings")
val files = parseFileSpecs(["file_a:a.txt file_b:dir/b.txt", "bad", ":missing", "file_c:"])
expect(files.len()).to_equal(2)
expect(files[0].fileId).to_equal("file_a")
expect(files[1].relativePath).to_equal("dir/b.txt")
```

</details>

#### should expose source-backed constants and error class

- Pin constants and class target
   - Expected: error.name equals `UploadNonRetriableError`
   - Expected: error.message equals `Upload canceled`
   - Expected: filesApiBetaHeader() equals `files-api-2025-04-14,oauth-2025-04-20`
   - Expected: filesApiSourceLinesModeled() equals `748`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin constants and class target")
val error = UploadNonRetriableError.new("Upload canceled")
expect(error.name).to_equal("UploadNonRetriableError")
expect(error.message).to_equal("Upload canceled")
expect(filesApiBetaHeader()).to_equal("files-api-2025-04-14,oauth-2025-04-20")
expect(filesApiSourceLinesModeled()).to_equal(748)
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

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/filesApi.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/api/filesApi.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
