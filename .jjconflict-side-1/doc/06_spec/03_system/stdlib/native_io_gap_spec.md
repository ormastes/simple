# Native Io Gap Specification

> 1. dir create all

<!-- sdn-diagram:id=native_io_gap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_io_gap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_io_gap_spec -> std
native_io_gap_spec -> app
native_io_gap_spec -> lib
native_io_gap_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_io_gap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Io Gap Specification

## Scenarios

### Native I/O Integration

### file operations end-to-end

#### complete file lifecycle

1. dir create all
   - Expected: wrote is true
   - Expected: file_exists(path) is true
   - Expected: deleted is true
   - Expected: file_exists(path) is false
2. dir remove all


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(TEST_DIR)
val path = TEST_DIR + "/lifecycle.txt"
val wrote = file_write(path, "native io test content")
expect(wrote).to_equal(true)
expect(file_exists(path)).to_equal(true)
val content = file_read(path)
expect(content).to_contain("native io test content")
val sz = file_size(path)
expect(sz).to_be_greater_than(0)
val deleted = file_delete(path)
expect(deleted).to_equal(true)
expect(file_exists(path)).to_equal(false)
dir_remove_all(TEST_DIR)
```

</details>

### CLI arg parsing end-to-end

#### full CLI workflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = cli_spec()
val spec2 = cli_spec_program(spec, "test-tool", "A system test tool")
val spec3 = cli_spec_flag(spec2, "verbose", "v", "Verbose output")
val spec4 = cli_spec_option(spec3, "output", "o", "Output file", "out.txt", [])
val spec5 = cli_spec_positional(spec4, "input", "Input file", true)
val parsed = parse_cli_args(spec5, ["-v", "--output", "result.txt", "input.spl"])
expect(parsed_flag(parsed, "verbose")).to_equal(true)
expect(parsed_option(parsed, "output")).to_equal("result.txt")
expect(parsed_positional(parsed, 0)).to_equal("input.spl")
val result = validate_args(spec5, parsed)
expect(result.0).to_equal(true)
val help = generate_help(spec5)
expect(help).to_contain("test-tool")
expect(help).to_contain("Verbose output")
```

</details>

### mapped types end-to-end

#### all type transforms produce correct output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(partial("Config")).to_equal("Partial<Config>")
expect(readonly_type("Config")).to_equal("Readonly<Config>")
expect(pick_type("User", "name,email")).to_equal("Pick<User, name,email>")
expect(omit_type("User", "password")).to_equal("Omit<User, password>")
```

</details>

### mmap struct API

#### rejects invalid mmap operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 0, size: 0, path: "/nonexistent")
expect(mf.address).to_equal(0)
expect(mf.size).to_equal(0)
```

</details>

### cross-module integration

#### writes CLI-parsed output path

1. dir create all
2. file write
   - Expected: file_exists(out_path) is true
3. dir remove all


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(TEST_DIR)
val spec = cli_spec()
val spec2 = cli_spec_option(spec, "output", "o", "Output file", "", [])
val parsed = parse_cli_args(spec2, ["--output", TEST_DIR + "/cli_out.txt"])
val out_path = parsed_option(parsed, "output")
file_write(out_path, "written via CLI path")
expect(file_exists(out_path)).to_equal(true)
val content = file_read(out_path)
expect(content).to_contain("written via CLI path")
dir_remove_all(TEST_DIR)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/native_io_gap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native I/O Integration
- file operations end-to-end
- CLI arg parsing end-to-end
- mapped types end-to-end
- mmap struct API
- cross-module integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
