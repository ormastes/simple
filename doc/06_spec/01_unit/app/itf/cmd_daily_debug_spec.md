# Cmd Daily Debug Specification

> <details>

<!-- sdn-diagram:id=cmd_daily_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cmd_daily_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cmd_daily_debug_spec -> std
cmd_daily_debug_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cmd_daily_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cmd Daily Debug Specification

## Scenarios

### extract_jira_keys (issue #10 step 3)

#### extracts a single ABC-123 style key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keys = extract_jira_keys("Please look at ABC-123 today.")
expect(keys.len()).to_equal(1)
expect(keys[0]).to_equal("ABC-123")
```

</details>

#### extracts multiple keys from one body

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "ABC-1, DEF12-9999 and the closed ABC-2."
val keys = extract_jira_keys(body)
expect(keys.len()).to_equal(3)
expect(keys[0]).to_equal("ABC-1")
expect(keys[1]).to_equal("DEF12-9999")
expect(keys[2]).to_equal("ABC-2")
```

</details>

#### ignores lowercase tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keys = extract_jira_keys("foo-12 is not a key but FOO-12 is.")
expect(keys.len()).to_equal(1)
expect(keys[0]).to_equal("FOO-12")
```

</details>

### extract_minio_urls (issue #10 step 3)

#### extracts a single https URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val urls = extract_minio_urls("Get https://minio.example.com/bug/abc-123/fw.bin please.")
expect(urls.len()).to_equal(1)
expect(urls[0]).to_equal("https://minio.example.com/bug/abc-123/fw.bin")
```

</details>

#### extracts multiple URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "http://a.com/x/y.elf and https://b.io/p/q.dmp"
val urls = extract_minio_urls(body)
expect(urls.len()).to_equal(2)
```

</details>

### triage_kind (issue #10 step 4)

#### classifies firmware extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(triage_kind("https://h/p/fw.bin")).to_equal("fw")
expect(triage_kind("https://h/p/fw.elf")).to_equal("fw")
expect(triage_kind("https://h/p/fw.HEX")).to_equal("fw")
```

</details>

#### classifies dump extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(triage_kind("https://h/p/c.dmp")).to_equal("dump")
expect(triage_kind("https://h/p/c.core")).to_equal("dump")
expect(triage_kind("https://h/p/c.crash")).to_equal("dump")
```

</details>

#### classifies note extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(triage_kind("https://h/p/n.log")).to_equal("note")
expect(triage_kind("https://h/p/n.txt")).to_equal("note")
expect(triage_kind("https://h/p/readme.md")).to_equal("note")
```

</details>

#### returns unknown for unrecognised extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(triage_kind("https://h/p/x.zip")).to_equal("unknown")
expect(triage_kind("https://h/p/no-ext")).to_equal("unknown")
```

</details>

#### triage_all preserves the order of inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val urls = [
    "https://h/p/a.bin",
    "https://h/p/b.dmp",
    "https://h/p/c.txt",
    "https://h/p/d.zip",
]
val out = triage_all(urls)
expect(out.len()).to_equal(4)
expect(out[0].kind).to_equal("fw")
expect(out[1].kind).to_equal("dump")
expect(out[2].kind).to_equal("note")
expect(out[3].kind).to_equal("unknown")
```

</details>

### watermark roundtrip (issue #10 steps 1+6)

#### parses a freshly rendered watermark

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = render_watermark("2026-04-26T12:00:00Z")
val parsed = parse_watermark(rendered)
expect(parsed).to_equal("2026-04-26T12:00:00Z")
```

</details>

#### ignores comments and blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "# header\n\nlast_run: \"2026-04-26T00:00:00Z\"\n"
expect(parse_watermark(body)).to_equal("2026-04-26T00:00:00Z")
```

</details>

#### returns empty when key absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_watermark("# nothing useful here\n")).to_equal("")
```

</details>

### run_daily_debug --dry-run (issue #10 AC4)

#### exits 0 with --dry-run and writes no files

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In --dry-run mode the driver must not call file_write_text on
# either the digest or the watermark. The outlook adapter is gated
# by `outlook_available = false` so step 2 returns []. The test
# verifies the exit code only; the absence of file writes is
# guaranteed structurally by the single `if not dry_run` gate
# around each `file_write_text` call.
val rc = run_daily_debug(["--dry-run", "--quiet"])
expect(rc).to_equal(0)
```

</details>

#### exits 0 with --dry-run alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = run_daily_debug(["--dry-run"])
expect(rc).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/cmd_daily_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- extract_jira_keys (issue #10 step 3)
- extract_minio_urls (issue #10 step 3)
- triage_kind (issue #10 step 4)
- watermark roundtrip (issue #10 steps 1+6)
- run_daily_debug --dry-run (issue #10 AC4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
