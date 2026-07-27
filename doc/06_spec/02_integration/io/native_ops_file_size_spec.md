# Native file size operations

> Verifies native file size and no-follow regular-file classification through the Simple file-ops facade.

<!-- sdn-diagram:id=native_ops_file_size_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_file_size_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_file_size_spec -> app
native_ops_file_size_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ops_file_size_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native file size operations

Verifies native file size and no-follow regular-file classification through the Simple file-ops facade.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/02_integration/io/native_ops_file_size_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies native file size and no-follow regular-file classification through the
Simple file-ops facade.

## Acceptance

- A temporary file can be written in the host temp directory.
- `file_size_raw` reports the expected size.
- Regular files pass while directories, missing paths, and symlinks fail.
- The temporary file is removed after the check.

## Scenarios

### Native File Ops

<details>
#### should get file size

- Write, measure, and remove one temporary file
   - Expected: writing and deleting the temporary file succeeds
   - Expected: `file_size_raw` returns `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write, measure, and remove one temporary file")
val suffix = "{getpid()}-{time_now_unix_micros()}"
val test_file = "{tmp}/simple_size_test-{suffix}.txt"

expect(file_write(test_file, "12345")).to_be(true)
expect(file_size_raw(test_file)).to_equal(5)
expect(file_delete(test_file)).to_be(true)
```

</details>

#### should classify a regular file without following a symlink

- Classify a regular file without following a symlink
   - Expected: target is a regular file
   - Expected: temp directory, missing path, and same-byte symlink are rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify a regular file without following a symlink")
val suffix = "{getpid()}-{time_now_unix_micros()}"
val target = "{tmp}/simple_regular_no_follow_target-{suffix}.txt"
val link = "{tmp}/simple_regular_no_follow_link-{suffix}.txt"
val missing = "{tmp}/simple_regular_no_follow_missing-{suffix}.txt"
file_delete(link)
file_delete(target)
file_delete(missing)
expect(file_write(target, "same-bytes")).to_be(true)
expect(file_is_regular_no_follow(target)).to_be(true)
expect(file_is_regular_no_follow(tmp)).to_be(false)
expect(file_is_regular_no_follow(missing)).to_be(false)
val (_, _, link_code) = if host_os() == "windows":
    process_run("cmd", ["/c", "mklink", link, target])
else:
    process_run("/bin/ln", ["-s", target, link])
expect(link_code).to_equal(0)
expect(file_hash_sha256(link)).to_equal(file_hash_sha256(target))
expect(file_is_regular_no_follow(link)).to_be(false)
expect(file_delete(link)).to_be(true)
expect(file_delete(target)).to_be(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
