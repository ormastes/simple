# Claude Full FileReadTool

> Checks modern FileReadTool parity for blocked paths, screenshot alternates,

<!-- sdn-diagram:id=FileReadTool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=FileReadTool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

FileReadTool_spec -> std
FileReadTool_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=FileReadTool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full FileReadTool

Checks modern FileReadTool parity for blocked paths, screenshot alternates,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern FileReadTool parity for blocked paths, screenshot alternates,
session files, schemas, token budget, text reads, PDFs, images, and listeners.

## Scenarios

### Claude full FileReadTool

#### should block device paths and proc fd aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(isBlockedDevicePath("/dev/zero")).to_equal(true)
expect(isBlockedDevicePath("/dev/fd/2")).to_equal(true)
expect(isBlockedDevicePath("/proc/123/fd/1")).to_equal(true)
expect(isBlockedDevicePath("/tmp/file.txt")).to_equal(false)
```

</details>

#### should derive alternate screenshot paths across thin-space variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alt = getAlternateScreenshotPath("/tmp/Screenshot 2026-01-01 at 10.30.00 AM.png")
expect(alt).to_contain("AM.png")
expect(alt).to_contain(thinSpace())
expect(getAlternateScreenshotPath(alt)).to_contain(" AM.png")
expect(getAlternateScreenshotPath("/tmp/readme.md")).to_equal("")
```

</details>

#### should register notify and unregister file read listeners

- var registry = FileReadListenerRegistry new
- registry = registerFileReadListener
- registry = notifyFileRead
   - Expected: registry.listeners.len() equals `1`
   - Expected: registry.listeners[0].calls equals `1`
   - Expected: registry.listeners[0].path equals `/tmp/a.txt`
- registry = unregisterFileReadListener
   - Expected: registry.listeners.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = FileReadListenerRegistry.new()
registry = registerFileReadListener(registry, "audit")
registry = notifyFileRead(registry, "/tmp/a.txt", "alpha")
expect(registry.listeners.len()).to_equal(1)
expect(registry.listeners[0].calls).to_equal(1)
expect(registry.listeners[0].path).to_equal("/tmp/a.txt")
registry = unregisterFileReadListener(registry, "audit")
expect(registry.listeners.len()).to_equal(0)
```

</details>

#### should expose token-limit error message parity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = MaxFileReadTokenExceededError.new(50000, 20000)
expect(err.name).to_equal("MaxFileReadTokenExceededError")
expect(err.message).to_contain("File content (50000 tokens) exceeds maximum allowed tokens (20000)")
expect(validateContentTokens(50000, 20000, true).tokenCount).to_equal(0)
expect(validateContentTokens(50000, 20000, false).tokenCount).to_equal(50000)
```

</details>

#### should detect session memory and transcript files under config dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detectSessionFileType("/home/u/.claude/session-memory/project.md", "/home/u/.claude")).to_equal("session_memory")
expect(detectSessionFileType("/home/u/.claude/projects/p.jsonl", "/home/u/.claude")).to_equal("session_transcript")
expect(detectSessionFileType("/home/u/other/projects/p.jsonl", "/home/u/.claude")).to_equal("")
```

</details>

#### should publish input output schema and line formatting helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(inputSchema()).to_contain("file_path|required")
expect(inputSchema()).to_contain("pages|optional")
expect(outputSchema()).to_contain("image(base64")
expect(pickLineFormatInstruction(3, 4)).to_contain("selected range")
expect(formatFileLines(["one", "two"], 7)).to_equal("7→one\n8→two")
```

</details>

#### should read text files with mitigation and memory freshness

- var registry = registerFileReadListener
   - Expected: out.typeName equals `text`
   - Expected: out.numLines equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = registerFileReadListener(FileReadListenerRegistry.new(), "audit")
val input = FileReadInput.textFile("/home/u/.claude/session-memory/project.md", "line one\nline two", "md", 2)
val out = callInner(input, registry, "/home/u/.claude", "claude-sonnet-4-5")
expect(out.typeName).to_equal("text")
expect(out.content).to_contain("line one")
expect(out.content).to_contain("cyber risk mitigation")
expect(out.freshnessPrefix).to_contain("Memory file last modified")
expect(out.numLines).to_equal(2)
```

</details>

#### should handle images with token budget compression and metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = FileReadInput(filePath: "/tmp/pic.jpg", content: "BASE64", ext: "jpg", offset: 1, limit: 0, pages: "", maxSizeBytes: 1000000, maxTokens: 100, tokenCount: 10, totalLines: 0, mtimeMs: 0, originalSize: 1000, width: 640, height: 480, pdfPages: 0, exists: true, supportedPdf: true, emptyImage: false)
val out = callInner(input, FileReadListenerRegistry.new(), "/home/u/.claude", "claude-sonnet-4-5")
expect(out.typeName).to_equal("image")
expect(out.image.mediaType).to_equal("image/jpeg")
expect(out.image.compression).to_equal("aggressive")
expect(out.newMessages[0]).to_contain("640x480")
expect(imageFiles()).to_equal(["png", "jpg", "jpeg", "gif", "webp"])
```

</details>

#### should handle PDF page extraction and unsupported full PDF branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pageInput = FileReadInput(filePath: "/tmp/a.pdf", content: "PDF", ext: "pdf", offset: 1, limit: 0, pages: "1-5", maxSizeBytes: 1000000, maxTokens: 20000, tokenCount: 10, totalLines: 0, mtimeMs: 0, originalSize: 1000, width: 0, height: 0, pdfPages: 20, exists: true, supportedPdf: false, emptyImage: false)
expect(callInner(pageInput, FileReadListenerRegistry.new(), "/home/u/.claude", "claude-sonnet-4-5").newMessages[0]).to_contain("pdf pages extracted")
val fullInput = FileReadInput(filePath: "/tmp/a.pdf", content: "PDF", ext: "pdf", offset: 1, limit: 0, pages: "", maxSizeBytes: 1000000, maxTokens: 20000, tokenCount: 10, totalLines: 0, mtimeMs: 0, originalSize: 1000, width: 0, height: 0, pdfPages: 20, exists: true, supportedPdf: false, emptyImage: false)
expect(callInner(fullInput, FileReadListenerRegistry.new(), "/home/u/.claude", "claude-sonnet-4-5").errorMessage).to_contain("Reading full PDFs is not supported")
```

</details>

#### should expose modeled source size

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fileReadToolSourceLinesModeled()).to_equal(1183)
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


</details>
