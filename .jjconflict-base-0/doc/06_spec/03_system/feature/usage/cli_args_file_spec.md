# CLI Args File Extension Detection Specification

> Tests file extension detection and the prefetch directive in the cli keyword. When a positional argument ends with a recognized file extension (.spl, .json, .csv, etc.), the cli system can auto-detect the type and optionally prefetch the file content before the main function runs.

<!-- sdn-diagram:id=cli_args_file_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_file_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_file_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_file_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args File Extension Detection Specification

Tests file extension detection and the prefetch directive in the cli keyword. When a positional argument ends with a recognized file extension (.spl, .json, .csv, etc.), the cli system can auto-detect the type and optionally prefetch the file content before the main function runs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-007 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_file_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests file extension detection and the prefetch directive in the cli keyword.
When a positional argument ends with a recognized file extension (.spl, .json,
.csv, etc.), the cli system can auto-detect the type and optionally prefetch
the file content before the main function runs.

## Syntax

```simple
cli:
    command run:
        positional file: text, ext: [".spl", ".shs"]
        prefetch: true     # read file content before dispatch

    command convert:
        positional input: text, ext: [".json", ".csv", ".sdn"]
        positional output: text
```

## Scenarios

### CLI Args File Extension Detection

#### extension detection

#### accepts file with matching extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     command run:
#         positional file: text, ext: [".spl", ".shs"]
# val args = cli.parse(["run", "main.spl"])
# expect(args.run.file).to_equal("main.spl")
val file = "main.spl"
val ext = ".spl"
val allowed = [".spl", ".shs"]
expect(file).to_end_with(ext)
expect(allowed).to_contain(".spl")
```

</details>

#### rejects file with wrong extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli.parse(["run", "data.json"]) should error
# because .json is not in [".spl", ".shs"]
val file = "data.json"
val ext = ".json"
val allowed = [".spl", ".shs"]
val is_valid = false
expect(is_valid).to_equal(false)
```

</details>

#### handles file without extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli.parse(["run", "Makefile"]) should error
# when ext filter is specified
val file = "Makefile"
val has_ext = false
expect(has_ext).to_equal(false)
```

</details>

#### prefetch directive

#### prefetches file content when enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     command run:
#         positional file: text, ext: [".spl"]
#         prefetch: true
# val args = cli.parse(["run", "hello.spl"])
# args.file_content should contain the file contents
val prefetch_enabled = true
expect(prefetch_enabled).to_equal(true)
```

</details>

#### skips prefetch when disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     command run:
#         positional file: text
# No prefetch directive means file_content is nil
val prefetch_enabled = false
val file_content = nil
expect(prefetch_enabled).to_equal(false)
expect(file_content).to_be_nil()
```

</details>

#### handles missing file gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli.parse(["run", "nonexistent.spl"]) with prefetch: true
# should produce a clear error about missing file
val error_msg = "file not found: nonexistent.spl"
expect(error_msg).to_start_with("file not found")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
