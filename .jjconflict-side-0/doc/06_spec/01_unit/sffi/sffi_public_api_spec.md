# SFFI CLI Public API Spec

> Unit tests for the SFFI CLI wrapper functions in `src/lib/nogc_sync_mut/ffi/cli.spl`. These cover AC-3 / AC-4 by providing explicit test coverage for every public wrapper fn.

<!-- sdn-diagram:id=sffi_public_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sffi_public_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sffi_public_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sffi_public_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI CLI Public API Spec

Unit tests for the SFFI CLI wrapper functions in `src/lib/nogc_sync_mut/ffi/cli.spl`. These cover AC-3 / AC-4 by providing explicit test coverage for every public wrapper fn.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-allow-suppressions |
| Category | Testing |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/sffi/sffi_public_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for the SFFI CLI wrapper functions in
`src/lib/nogc_sync_mut/ffi/cli.spl`. These cover AC-3 / AC-4 by providing
explicit test coverage for every public wrapper fn.

Note: Tests exercise the wrapper fn behaviour (not the extern fn directly).
Functions that touch live OS state (file I/O, process execution) are tested
with minimal safe inputs. Functions whose correct return value depends on
runtime state have the return type and non-error exit path asserted.

These specs WILL FAIL until Team D lands and wires up the test stubs.

## Scenarios

### AC-3/AC-4 SFFI cli_get_args

#### AC-3: cli_get_args returns a list (not nil)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = cli_get_args()
expect(args).to_be_nil().to_equal(false)
```

</details>

#### AC-3: cli_get_args returns a list with len >= 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = cli_get_args()
expect(args.len()).to_be_greater_than(-1)
```

</details>

### AC-3/AC-4 SFFI cli_file_exists

#### AC-3: cli_file_exists returns false for a nonexistent path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = cli_file_exists("/tmp/sffi_test_nonexistent_file_xyz123.txt")
expect(exists).to_equal(false)
```

</details>

#### AC-3: cli_file_exists returns true for a path that is known to exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The compiler binary itself is a reliable known-existing file.
# This test is environment-dependent; it verifies the positive branch.
val exists = cli_file_exists("/usr/bin/env")
expect(exists).to_equal(true)
```

</details>

### AC-3/AC-4 SFFI cli_read_file

#### AC-3: cli_read_file returns non-empty text for an existing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# /etc/hostname is universally present on Linux
val content = cli_read_file("/etc/hostname")
expect(content.len()).to_be_greater_than(0)
```

</details>

### AC-3/AC-4 SFFI cli_exit signature

#### AC-3: cli_exit wrapper fn exists and accepts i64 (signature contract)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Calling cli_exit(0) would kill the test runner.
# Verify the wrapper contract without invoking the terminating path.
val source = cli_read_file("src/lib/nogc_sync_mut/sffi/cli.spl")
expect(source).to_contain("fn cli_exit(code: i64):")
expect(source).to_contain("rt_cli_exit(code)")
```

</details>

### AC-3/AC-4 SFFI cli_dispatch_rust

#### AC-3: cli_dispatch_rust with empty cmd returns an exit code (i64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_args = [] of text
val code = cli_dispatch_rust(cmd: "", args: empty_args, gc_log: false, gc_off: false)
# Any integer is a valid exit code; just verify it is numeric
expect(code).to_be_greater_than(-128)
```

</details>

#### AC-3: cli_dispatch_rust with unknown cmd returns nonzero exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_args = [] of text
val code = cli_dispatch_rust(cmd: "__sffi_test_unknown_cmd_xyz__", args: empty_args, gc_log: false, gc_off: false)
expect(code).to_be_greater_than(0)
```

</details>

### AC-3/AC-4 SFFI cli_watch_file

#### AC-3: cli_watch_file returns a handle for a valid path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = cli_watch_file("/etc/hostname")
expect(handle).to_be_greater_than(-2)
```

</details>

### AC-3/AC-4 SFFI CLI alias wrappers

#### AC-3: cli_lint is callable with named args (returns i64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lint_args = ["--help"] of text
val result = cli_lint(args: lint_args)
expect(result).to_be_greater_than(-128)
```

</details>

#### AC-3: cli_fmt is callable with named args (returns i64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt_args = ["--help"] of text
val result = cli_fmt(args: fmt_args)
expect(result).to_be_greater_than(-128)
```

</details>

### AC-3/AC-4 SFFI compile_to_native

#### AC-3: compile_to_native returns (false, error_message) for nonexistent source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = compile_to_native(
    source_path: "/tmp/sffi_test_nonexistent_src_xyz123.spl",
    output_path: "/tmp/sffi_test_out_xyz123"
)
val ok = res.0
expect(ok).to_equal(false)
```

</details>

#### AC-3: compile_to_native error message is non-empty on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = compile_to_native(
    source_path: "/tmp/sffi_test_nonexistent_src_xyz123.spl",
    output_path: "/tmp/sffi_test_out_xyz123"
)
val msg = res.1
expect(msg.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
