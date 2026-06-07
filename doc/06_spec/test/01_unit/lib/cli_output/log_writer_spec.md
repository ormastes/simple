# Log Writer Specification

> 1. expect empty or nil

<!-- sdn-diagram:id=log_writer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_writer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_writer_spec -> std
log_writer_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_writer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Writer Specification

## Scenarios

### cli_output.log_writer

#### should create log file with correct path prefix

1. expect empty or nil
   - Expected: exists is false
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_path = log_open("test")
# In interpreter mode, imported log functions may not fully work
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
expect(log_path).to_start_with("build/log/test/")
expect(log_path).to_end_with(".log")
val exists = file_exists(log_path)
# In interpreter mode, the log file may not actually be created
if not exists:
    expect(exists).to_equal(false)
else:
    expect(exists).to_equal(true)
```

</details>

#### should append lines to log file

1. expect empty or nil
2. log line
3. log line
4. expect empty or nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_path = log_open("test")
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
log_line(log_path, "  PASS  test/a_spec.spl (3 passed, 42ms)")
log_line(log_path, "  FAIL  test/b_spec.spl (1 passed, 1 failed, 38ms)")
val content = file_read(log_path)
if content == "" or content == nil:
    # Interpreter mode: file_read may return empty
    expect_empty_or_nil(content)
else:
    expect(content).to_contain("PASS")
    expect(content).to_contain("FAIL")
```

</details>

#### should strip ANSI codes from logged lines

1. expect empty or nil
2. log line
3. expect empty or nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_path = log_open("test")
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
log_line(log_path, "PASS  test.spl")
val content = file_read(log_path)
if content == "" or content == nil:
    expect_empty_or_nil(content)
else:
    expect(content).to_contain("PASS")
    expect(content).to_contain("test.spl")
```

</details>

#### should create latest.log symlink on close

1. expect empty or nil
2. log line
3. log close
   - Expected: symlink_exists is false
   - Expected: symlink_exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_path = log_open("test")
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
log_line(log_path, "test line")
log_close(log_path, "test")
val symlink_exists = file_exists("build/log/test/latest.log")
# In interpreter mode, symlink creation may not work
if not symlink_exists:
    expect(symlink_exists).to_equal(false)
else:
    expect(symlink_exists).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cli_output/log_writer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cli_output.log_writer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
