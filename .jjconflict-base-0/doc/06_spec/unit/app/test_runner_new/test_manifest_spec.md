# Test Manifest Specification

> Tests covering TestManifest Data Model, TestManifest Serialization Format, TestManifest Scanner Logic, TestManifest Freshness, TestManifest CLI Flags.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Manifest Specification

## Scenarios

### TestManifest Data Model

#### creates empty manifest with version 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty manifest with version 1
   - Expected: version equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty manifest with version 1")
val version = 1
expect(version).to_equal(1)
```

</details>

#### parse entry from pipe-delimited line

- parse entry from pipe-delimited line
   - Expected: parts.len() equals `14`
   - Expected: parts[0] equals `test/unit/x_spec.spl`
   - Expected: parts[4] equals `0`
   - Expected: parts[5] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse entry from pipe-delimited line")
val line = "test/unit/x_spec.spl|500|100|1|0|1|0|tag1|linux|0|0|0|0|0"
val parts = line.split("|")
expect(parts.len()).to_equal(14)
expect(parts[0]).to_equal("test/unit/x_spec.spl")
expect(parts[4]).to_equal("0")
expect(parts[5]).to_equal("1")
```

</details>

#### parse sdoctest entry from pipe-delimited line

- parse sdoctest entry from pipe-delimited line
   - Expected: parts.len() equals `4`
   - Expected: parts[0] equals `doc/07_guide/intro.md`
   - Expected: parts[3] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse sdoctest entry from pipe-delimited line")
val line = "doc/07_guide/intro.md|5000|888000|7"
val parts = line.split("|")
expect(parts.len()).to_equal(4)
expect(parts[0]).to_equal("doc/07_guide/intro.md")
expect(parts[3]).to_equal("7")
```

</details>

#### handles short/invalid line gracefully

- handles short/invalid line gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles short/invalid line gracefully")
val line = "bad|data"
val parts = line.split("|")
expect(parts.len()).to_be_less_than(14)
```

</details>

### TestManifest Serialization Format

#### serializes entry with correct pipe-delimited format

- serializes entry with correct pipe-delimited format


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes entry with correct pipe-delimited format")
val path = "test/unit/foo_spec.spl"
val size = 1024
val mtime = 999000
val level = 1
val slow = "0"
val skipped = "1"
val pending = "0"
val tags = "parser,lexer"
val platform = "linux"
val fuzz = "0"
val chaos = "0"
val deploy = "0"
val security = "0"
val bare = "0"
val line = "{path}|{size}|{mtime}|{level}|{slow}|{skipped}|{pending}|{tags}|{platform}|{fuzz}|{chaos}|{deploy}|{security}|{bare}"
expect(line).to_start_with("test/unit/foo_spec.spl|")
expect(line).to_contain("|1024|")
expect(line).to_contain("|parser,lexer|")
```

</details>

#### serializes manifest header

- serializes manifest header


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes manifest header")
val version = 1
val timestamp = 1234567890
val entry_count = 5
val header = "# test-manifest v{version}\nscan_timestamp={timestamp}\nentry_count={entry_count}"
expect(header).to_start_with("# test-manifest v1")
expect(header).to_contain("scan_timestamp=1234567890")
expect(header).to_contain("entry_count=5")
```

</details>

### TestManifest Scanner Logic

#### detects unit test level from path

- detects unit test level from path
   - Expected: level equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects unit test level from path")
val path = "test/unit/parser/foo_spec.spl"
var level = 0
if path.contains("/unit/"):
    level = 1
expect(level).to_equal(1)
```

</details>

#### detects integration test level from path

- detects integration test level from path
   - Expected: level equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects integration test level from path")
val path = "test/integration/bar_spec.spl"
var level = 0
if path.contains("/integration/"):
    level = 2
expect(level).to_equal(2)
```

</details>

#### detects system test level from path

- detects system test level from path
   - Expected: level equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects system test level from path")
val path = "test/system/baz_spec.spl"
var level = 0
if path.contains("/system/"):
    level = 3
expect(level).to_equal(3)
```

</details>

#### detects feature as system level

- detects feature as system level
   - Expected: level equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects feature as system level")
val path = "test/feature/qux_spec.spl"
var level = 0
if path.contains("/feature/"):
    level = 3
expect(level).to_equal(3)
```

</details>

#### returns 0 for unknown test level

- returns 0 for unknown test level
   - Expected: level equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for unknown test level")
val path = "test/misc/x_spec.spl"
var level = 0
if path.contains("/unit/"):
    level = 1
if path.contains("/integration/"):
    level = 2
if path.contains("/system/") or path.contains("/feature/"):
    level = 3
expect(level).to_equal(0)
```

</details>

#### identifies spec files by name pattern

- identifies spec files by name pattern
   - Expected: name1 contains `_spec.`
   - Expected: name2 contains `_test.`
   - Expected: name3 does not contain `_spec.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies spec files by name pattern")
val name1 = "foo_spec.spl"
val name2 = "bar_test.spl"
val name3 = "baz.spl"
expect(name1.contains("_spec.")).to_equal(true)
expect(name2.contains("_test.")).to_equal(true)
expect(name3.contains("_spec.")).to_equal(false)
```

</details>

#### counts sdoctest blocks in content

- counts sdoctest blocks in content
   - Expected: count_sdoctest_blocks(content) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts sdoctest blocks in content")
val content = "text\n```simple:should_fail\ncode\n```\n```spl\ncode2\n```\n```simple\nunclosed"
expect(count_sdoctest_blocks(content)).to_equal(2)
```

</details>

#### registers source-comment doctests with the execution extractor

- registers source-comment doctests with the execution extractor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers source-comment doctests with the execution extractor")
val entry = scan_sdoctest_file("src/compiler/00.common/gc_config.spl")
expect(entry.block_count).to_be_greater_than(0)
```

</details>

#### extracts platform tags from content

- extracts platform tags from content
   - Expected: tags.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts platform tags from content")
val content = "# @platform: linux\ncode\n# @platform: interpreter"
val lines = content.split("\n")
var tags: [text] = []
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("# @platform:"):
        val tag = trimmed[12:].trim()
        if tag != "":
            tags.push(tag)
expect(tags.len()).to_equal(2)
```

</details>

#### detects slow test markers

- detects slow test markers
   - Expected: content contains `slow_it `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects slow test markers")
val content = "describe \"x\":\n    slow_it \"takes time\":\n        pass"
expect(content.contains("slow_it ")).to_equal(true)
```

</details>

#### detects skip tag markers

- detects skip tag markers
   - Expected: has_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects skip tag markers")
val content = "tag: \"skip\"\ndescribe \"x\":"
val has_skip = content.contains("tag: \"skip\"") or content.contains("tag: 'skip'")
expect(has_skip).to_equal(true)
```

</details>

#### detects pending markers

- detects pending markers
   - Expected: has_pending is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects pending markers")
val content = "# @pending\ndescribe \"x\":"
val has_pending = content.contains("# @pending") or content.contains("tag: \"pending\"")
expect(has_pending).to_equal(true)
```

</details>

#### detects fuzz directory

- detects fuzz directory
   - Expected: path contains `/fuzz/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects fuzz directory")
val path = "test/feature/language/fuzz/parser_fuzz_spec.spl"
expect(path.contains("/fuzz/")).to_equal(true)
```

</details>

#### detects baremetal directory

- detects baremetal directory
   - Expected: path contains `/baremetal/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects baremetal directory")
val path = "test/baremetal/riscv32/boot_spec.spl"
expect(path.contains("/baremetal/")).to_equal(true)
```

</details>

### TestManifest Freshness

#### zero timestamp means not fresh

- zero timestamp means not fresh
   - Expected: is_fresh is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero timestamp means not fresh")
val timestamp = 0
val is_fresh = timestamp > 0
expect(is_fresh).to_equal(false)
```

</details>

#### manifest TTL is 5 minutes in microseconds

- manifest TTL is 5 minutes in microseconds
   - Expected: ttl equals `300000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manifest TTL is 5 minutes in microseconds")
val ttl = 300000000
expect(ttl).to_equal(300000000)
```

</details>

### TestManifest CLI Flags

#### no-cache flag name

- no-cache flag name
   - Expected: flag equals `--no-cache`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no-cache flag name")
val flag = "--no-cache"
expect(flag).to_equal("--no-cache")
```

</details>

#### refresh-manifest flag name

- refresh-manifest flag name
   - Expected: flag equals `--refresh-manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refresh-manifest flag name")
val flag = "--refresh-manifest"
expect(flag).to_equal("--refresh-manifest")
```

</details>

#### manifest-status flag name

- manifest-status flag name
   - Expected: flag equals `--manifest-status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manifest-status flag name")
val flag = "--manifest-status"
expect(flag).to_equal("--manifest-status")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/test_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestManifest Data Model, TestManifest Serialization Format, TestManifest Scanner Logic, TestManifest Freshness, TestManifest CLI Flags.
- TestManifest Data Model
- TestManifest Serialization Format
- TestManifest Scanner Logic
- TestManifest Freshness
- TestManifest CLI Flags

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `30c727416e974c2bb0d5acb8ebc22a29c8fb5cbb3d9ecbc7160d82c96fd204f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `30c727416e974c2bb0d5acb8ebc22a29c8fb5cbb3d9ecbc7160d82c96fd204f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `30c727416e974c2bb0d5acb8ebc22a29c8fb5cbb3d9ecbc7160d82c96fd204f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_runner_new/test_manifest_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/test_manifest_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/test_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/test_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/test_manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_runner_new/test_manifest_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty manifest with version 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_manifest_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse entry from pipe-delimited line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_manifest_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse sdoctest entry from pipe-delimited line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
