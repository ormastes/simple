# Fileio Simple Specification

> <details>

<!-- sdn-diagram:id=fileio_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fileio_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fileio_simple_spec -> std
fileio_simple_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fileio_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fileio Simple Specification

## Scenarios

### FileIO Simple - Protection Rules

#### protects critical files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_protection("CLAUDE.md", "write")).to_contain("DENIED")
expect(check_protection("CLAUDE.md", "read")).to_equal("ALLOWED")
```

</details>

#### redirects test files and shell scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_protection("test_file.txt", "write")).to_contain("REDIRECT")
expect(check_protection("mcp_test_output.txt", "write")).to_contain("REDIRECT")
expect(check_protection("script.sh", "write")).to_contain("REDIRECT")
```

</details>

#### denies version control and lock files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_protection(".git/config", "write")).to_contain("DENIED")
expect(check_protection(".jj/abc", "write")).to_contain("DENIED")
expect(check_protection("cache.lock", "write")).to_contain("DENIED")
```

</details>

#### requires atomic writes for sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_protection("data.sdn", "write")).to_contain("ATOMIC")
```

</details>

#### allows build and tmp directories

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_protection("build/output.txt", "write")).to_equal("ALLOWED")
expect(check_protection("tmp/output.txt", "write")).to_equal("ALLOWED")
expect(check_protection("tmp/fileio_temp/output.txt", "write")).to_equal("ALLOWED")
```

</details>

#### denies root-level files by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_protection("root.txt", "write")).to_contain("DENIED")
```

</details>

#### allows subdirectories by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_protection("src/file.txt", "write")).to_equal("ALLOWED")
```

</details>

### FileIO Simple - Handlers

#### handles safe_write in each mode

1. shell
   - Expected: allowed.starts_with("OK:" ) is true
   - Expected: denied.starts_with("ERROR:" ) is true
   - Expected: atomic contains `Atomic write required`
   - Expected: redirected contains `temp`
   - Expected: file_exists("tmp/fileio_temp/test_file.txt") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shell("mkdir -p tmp/fileio_temp")
val allowed = handle_safe_write("tmp/mcp_simple_allowed.txt", "ok")
expect(allowed.starts_with("OK:" )).to_equal(true)
val denied = handle_safe_write("CLAUDE.md", "x")
expect(denied.starts_with("ERROR:" )).to_equal(true)
val atomic = handle_safe_write("data.sdn", "x")
expect(atomic.contains("Atomic write required")).to_equal(true)
val redirected = handle_safe_write("test_file.txt", "x")
expect(redirected.contains("temp" )).to_equal(true)
expect(file_exists("tmp/fileio_temp/test_file.txt")).to_equal(true)
```

</details>

#### handles safe_read

1. file write
   - Expected: ok.starts_with("OK:" ) is true
   - Expected: missing contains `File not found`
   - Expected: denied.starts_with("ERROR:" ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/mcp_simple_read.txt"
file_write(path, "read")
val ok = handle_safe_read(path)
expect(ok.starts_with("OK:" )).to_equal(true)
val missing = handle_safe_read("/tmp/mcp_simple_missing.txt")
expect(missing.contains("File not found")).to_equal(true)
val denied = handle_safe_read("README.md")
expect(denied.starts_with("ERROR:" )).to_equal(true)
```

</details>

#### handles check_protection handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = handle_check_protection("data.sdn")
expect(resp.contains("PROTECTION:" )).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp/fileio_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FileIO Simple - Protection Rules
- FileIO Simple - Handlers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
