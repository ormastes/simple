# Claude Full FileReadTool

> Purpose: should block device paths and proc fd aliases

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full FileReadTool

Purpose: should block device paths and proc fd aliases

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should block device paths and proc fd aliases
Audience: compiler and tooling engineers who maintain this spec

# Claude Full FileReadTool

Checks modern FileReadTool parity for blocked paths, screenshot alternates,
session files, schemas, token budget, text reads, PDFs, images, and listeners.

## Scenarios

### Claude full FileReadTool

#### should block device paths and proc fd aliases

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should block device paths and proc fd aliases
- Verify: should block device paths and proc fd aliases
   - Expected: isBlockedDevicePath("/dev/zero") is true
   - Expected: isBlockedDevicePath("/dev/fd/2") is true
   - Expected: isBlockedDevicePath("/proc/123/fd/1") is true
   - Expected: isBlockedDevicePath("/tmp/file.txt") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should block device paths and proc fd aliases")
step("Verify: should block device paths and proc fd aliases")
# @req: REQ-TOOLS-File-001
expect(isBlockedDevicePath("/dev/zero")).to_equal(true)
expect(isBlockedDevicePath("/dev/fd/2")).to_equal(true)
expect(isBlockedDevicePath("/proc/123/fd/1")).to_equal(true)
expect(isBlockedDevicePath("/tmp/file.txt")).to_equal(false)
```

</details>

#### should derive alternate screenshot paths across thin-space variants

- should derive alternate screenshot paths across thin-space variants
- Verify: should derive alternate screenshot paths across thin-space variants
   - Expected: getAlternateScreenshotPath("/tmp/readme.md") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive alternate screenshot paths across thin-space variants")
step("Verify: should derive alternate screenshot paths across thin-space variants")
# @req: REQ-TOOLS-File-001
val alt = getAlternateScreenshotPath("/tmp/Screenshot 2026-01-01 at 10.30.00 AM.png")
expect(alt).to_contain("AM.png")
expect(alt).to_contain(thinSpace())
expect(getAlternateScreenshotPath(alt)).to_contain(" AM.png")
expect(getAlternateScreenshotPath("/tmp/readme.md")).to_equal("")
```

</details>

#### should register notify and unregister file read listeners

- should register notify and unregister file read listeners
- Verify: should register notify and unregister file read listeners
   - Expected: registry.listeners.len() equals `1`
   - Expected: registry.listeners[0].calls equals `1`
   - Expected: registry.listeners[0].path equals `/tmp/a.txt`
   - Expected: registry.listeners.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should register notify and unregister file read listeners")
step("Verify: should register notify and unregister file read listeners")
# @req: REQ-TOOLS-File-001
var registry = FileReadListenerRegistry.new()
registry = registerFileReadListener(registry, "audit")
registry = notifyFileRead(registry, "/tmp/a.txt", "alpha")
expect(registry.listeners.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(registry.listeners[0].calls).to_equal(1)  # oracle: value fixed by the spec contract
expect(registry.listeners[0].path).to_equal("/tmp/a.txt")
registry = unregisterFileReadListener(registry, "audit")
expect(registry.listeners.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should expose token-limit error message parity

- should expose token-limit error message parity
- Verify: should expose token-limit error message parity
   - Expected: err.name equals `MaxFileReadTokenExceededError`
   - Expected: validateContentTokens(50000, 20000, true).tokenCount equals `0`
   - Expected: validateContentTokens(50000, 20000, false).tokenCount equals `50000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose token-limit error message parity")
step("Verify: should expose token-limit error message parity")
# @req: REQ-TOOLS-File-001
val err = MaxFileReadTokenExceededError.new(50000, 20000)
expect(err.name).to_equal("MaxFileReadTokenExceededError")
expect(err.message).to_contain("File content (50000 tokens) exceeds maximum allowed tokens (20000)")
expect(validateContentTokens(50000, 20000, true).tokenCount).to_equal(0)  # oracle: value fixed by the spec contract
expect(validateContentTokens(50000, 20000, false).tokenCount).to_equal(50000)  # oracle: value fixed by the spec contract
```

</details>

#### should detect session memory and transcript files under config dir

- should detect session memory and transcript files under config dir
- Verify: should detect session memory and transcript files under config dir
   - Expected: detectSessionFileType("/home/u/.claude/session-memory/project.md", "/home/u/.claude") equals `session_memory`
   - Expected: detectSessionFileType("/home/u/.claude/projects/p.jsonl", "/home/u/.claude") equals `session_transcript`
   - Expected: detectSessionFileType("/home/u/other/projects/p.jsonl", "/home/u/.claude") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect session memory and transcript files under config dir")
step("Verify: should detect session memory and transcript files under config dir")
# @req: REQ-TOOLS-File-001
expect(detectSessionFileType("/home/u/.claude/session-memory/project.md", "/home/u/.claude")).to_equal("session_memory")
expect(detectSessionFileType("/home/u/.claude/projects/p.jsonl", "/home/u/.claude")).to_equal("session_transcript")
expect(detectSessionFileType("/home/u/other/projects/p.jsonl", "/home/u/.claude")).to_equal("")
```

</details>

#### should publish input output schema and line formatting helpers

- should publish input output schema and line formatting helpers
- Verify: should publish input output schema and line formatting helpers
   - Expected: formatFileLines(["one", "two"], 7) equals `7→one\n8→two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should publish input output schema and line formatting helpers")
step("Verify: should publish input output schema and line formatting helpers")
# @req: REQ-TOOLS-File-001
expect(inputSchema()).to_contain("file_path|required")
expect(inputSchema()).to_contain("pages|optional")
expect(outputSchema()).to_contain("image(base64")
expect(pickLineFormatInstruction(3, 4)).to_contain("selected range")
expect(formatFileLines(["one", "two"], 7)).to_equal("7→one\n8→two")
```

</details>

#### should read text files with mitigation and memory freshness

- should read text files with mitigation and memory freshness
- Verify: should read text files with mitigation and memory freshness
   - Expected: out.typeName equals `text`
   - Expected: out.numLines equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should read text files with mitigation and memory freshness")
step("Verify: should read text files with mitigation and memory freshness")
# @req: REQ-TOOLS-File-001
var registry = registerFileReadListener(FileReadListenerRegistry.new(), "audit")
val input = FileReadInput.textFile("/home/u/.claude/session-memory/project.md", "line one\nline two", "md", 2)
val out = callInner(input, registry, "/home/u/.claude", "claude-sonnet-4-5")
expect(out.typeName).to_equal("text")
expect(out.content).to_contain("line one")
expect(out.content).to_contain("cyber risk mitigation")
expect(out.freshnessPrefix).to_contain("Memory file last modified")
expect(out.numLines).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should handle images with token budget compression and metadata

- should handle images with token budget compression and metadata
- Verify: should handle images with token budget compression and metadata
   - Expected: out.typeName equals `image`
   - Expected: out.image.mediaType equals `image/jpeg`
   - Expected: out.image.compression equals `aggressive`
   - Expected: imageFiles() equals `["png", "jpg", "jpeg", "gif", "webp"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle images with token budget compression and metadata")
step("Verify: should handle images with token budget compression and metadata")
# @req: REQ-TOOLS-File-001
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

- should handle PDF page extraction and unsupported full PDF branch
- Verify: should handle PDF page extraction and unsupported full PDF branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle PDF page extraction and unsupported full PDF branch")
step("Verify: should handle PDF page extraction and unsupported full PDF branch")
# @req: REQ-TOOLS-File-001
val pageInput = FileReadInput(filePath: "/tmp/a.pdf", content: "PDF", ext: "pdf", offset: 1, limit: 0, pages: "1-5", maxSizeBytes: 1000000, maxTokens: 20000, tokenCount: 10, totalLines: 0, mtimeMs: 0, originalSize: 1000, width: 0, height: 0, pdfPages: 20, exists: true, supportedPdf: false, emptyImage: false)
expect(callInner(pageInput, FileReadListenerRegistry.new(), "/home/u/.claude", "claude-sonnet-4-5").newMessages[0]).to_contain("pdf pages extracted")
val fullInput = FileReadInput(filePath: "/tmp/a.pdf", content: "PDF", ext: "pdf", offset: 1, limit: 0, pages: "", maxSizeBytes: 1000000, maxTokens: 20000, tokenCount: 10, totalLines: 0, mtimeMs: 0, originalSize: 1000, width: 0, height: 0, pdfPages: 20, exists: true, supportedPdf: false, emptyImage: false)
expect(callInner(fullInput, FileReadListenerRegistry.new(), "/home/u/.claude", "claude-sonnet-4-5").errorMessage).to_contain("Reading full PDFs is not supported")
```

</details>

#### should expose modeled source size

- should expose modeled source size
- Verify: should expose modeled source size
   - Expected: fileReadToolSourceLinesModeled() equals `1183`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose modeled source size")
step("Verify: should expose modeled source size")
# @req: REQ-TOOLS-File-001
expect(fileReadToolSourceLinesModeled()).to_equal(1183)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-File-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6f343fa4641f4af4673d5cbe74e5e1b2f8ef752afa041adb7d83e2bc62c2a0fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f343fa4641f4af4673d5cbe74e5e1b2f8ef752afa041adb7d83e2bc62c2a0fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f343fa4641f4af4673d5cbe74e5e1b2f8ef752afa041adb7d83e2bc62c2a0fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should block device paths and proc fd aliases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should block device paths and proc fd aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive alternate screenshot paths across thin-space variants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should derive alternate screenshot paths across thin-space variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should register notify and unregister file read listeners' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should register notify and unregister file read listeners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose token-limit error message parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect session memory and transcript files under config dir' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/FileReadTool/FileReadTool_spec.spl:80:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish input output schema and line formatting helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
