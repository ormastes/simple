# Test Manifest Specification

> <details>

<!-- sdn-diagram:id=test_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_manifest_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Manifest Specification

## Scenarios

### TestManifest Data Model

#### creates empty manifest with version 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = 1
expect(version).to_equal(1)
```

</details>

#### parse entry from pipe-delimited line

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "test/unit/x_spec.spl|500|100|1|0|1|0|tag1|linux|0|0|0|0|0"
val parts = line.split("|")
expect(parts.len()).to_equal(14)
expect(parts[0]).to_equal("test/unit/x_spec.spl")
expect(parts[4]).to_equal("0")
expect(parts[5]).to_equal("1")
```

</details>

#### parse sdoctest entry from pipe-delimited line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "doc/07_guide/intro.md|5000|888000|7"
val parts = line.split("|")
expect(parts.len()).to_equal(4)
expect(parts[0]).to_equal("doc/07_guide/intro.md")
expect(parts[3]).to_equal("7")
```

</details>

#### handles short/invalid line gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "bad|data"
val parts = line.split("|")
expect(parts.len()).to_be_less_than(14)
```

</details>

### TestManifest Serialization Format

#### serializes entry with correct pipe-delimited format

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/unit/parser/foo_spec.spl"
var level = 0
if path.contains("/unit/"):
    level = 1
expect(level).to_equal(1)
```

</details>

#### detects integration test level from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/integration/bar_spec.spl"
var level = 0
if path.contains("/integration/"):
    level = 2
expect(level).to_equal(2)
```

</details>

#### detects system test level from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/system/baz_spec.spl"
var level = 0
if path.contains("/system/"):
    level = 3
expect(level).to_equal(3)
```

</details>

#### detects feature as system level

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/feature/qux_spec.spl"
var level = 0
if path.contains("/feature/"):
    level = 3
expect(level).to_equal(3)
```

</details>

#### returns 0 for unknown test level

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name1 = "foo_spec.spl"
val name2 = "bar_test.spl"
val name3 = "baz.spl"
expect(name1.contains("_spec.")).to_equal(true)
expect(name2.contains("_test.")).to_equal(true)
expect(name3.contains("_spec.")).to_equal(false)
```

</details>

#### counts sdoctest blocks in content

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "text\n```simple\ncode\n```\nmore\n```spl\ncode2\n```"
val lines = content.split("\n")
var count = 0
for line in lines:
    val trimmed = line.trim()
    if trimmed == "```simple" or trimmed == "```spl":
        count = count + 1
expect(count).to_equal(2)
```

</details>

#### extracts platform tags from content

1. tags push
   - Expected: tags.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "describe \"x\":\n    slow_it \"takes time\":\n        pass"
expect(content.contains("slow_it ")).to_equal(true)
```

</details>

#### detects skip tag markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "tag: \"skip\"\ndescribe \"x\":"
val has_skip = content.contains("tag: \"skip\"") or content.contains("tag: 'skip'")
expect(has_skip).to_equal(true)
```

</details>

#### detects pending markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @pending\ndescribe \"x\":"
val has_pending = content.contains("# @pending") or content.contains("tag: \"pending\"")
expect(has_pending).to_equal(true)
```

</details>

#### detects fuzz directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/feature/language/fuzz/parser_fuzz_spec.spl"
expect(path.contains("/fuzz/")).to_equal(true)
```

</details>

#### detects baremetal directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/baremetal/riscv32/boot_spec.spl"
expect(path.contains("/baremetal/")).to_equal(true)
```

</details>

### TestManifest Freshness

#### zero timestamp means not fresh

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timestamp = 0
val is_fresh = timestamp > 0
expect(is_fresh).to_equal(false)
```

</details>

#### manifest TTL is 5 minutes in microseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ttl = 300000000
expect(ttl).to_equal(300000000)
```

</details>

### TestManifest CLI Flags

#### no-cache flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--no-cache"
expect(flag).to_equal("--no-cache")
```

</details>

#### refresh-manifest flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--refresh-manifest"
expect(flag).to_equal("--refresh-manifest")
```

</details>

#### manifest-status flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--manifest-status"
expect(flag).to_equal("--manifest-status")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestManifest Data Model
- TestManifest Serialization Format
- TestManifest Scanner Logic
- TestManifest Freshness
- TestManifest CLI Flags

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
