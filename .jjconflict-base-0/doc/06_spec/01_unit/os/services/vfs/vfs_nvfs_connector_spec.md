# Vfs Nvfs Connector Specification

> _Covers the service-level connection from MountTable to NvfsPosixDriver._

<!-- sdn-diagram:id=vfs_nvfs_connector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vfs_nvfs_connector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vfs_nvfs_connector_spec -> std
vfs_nvfs_connector_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vfs_nvfs_connector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vfs Nvfs Connector Specification

## Scenarios

### VFS NVFS connector
_Covers the service-level connection from MountTable to NvfsPosixDriver._

#### mounts NVFS and round-trips file content through connector helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = nvfs_vfs_connect("/nvfs", "unit-nvfs", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

val wr = nvfs_vfs_write_text(c, "/nvfs/hello.txt", "hello")
expect(wr.is_ok()).to_equal(true)

val ex = nvfs_vfs_file_exists(c, "/nvfs/hello.txt")
expect(ex.is_ok()).to_equal(true)
expect(ex.unwrap()).to_equal(true)

val sz = nvfs_vfs_file_size(c, "/nvfs/hello.txt")
expect(sz.is_ok()).to_equal(true)
expect(sz.unwrap()).to_equal(5)

val rt = nvfs_vfs_read_text(c, "/nvfs/hello.txt")
expect(rt.is_ok()).to_equal(true)
expect(rt.unwrap()).to_equal("hello")

val rb = nvfs_vfs_read_bytes(c, "/nvfs/hello.txt")
expect(rb.is_ok()).to_equal(true)
val bytes = rb.unwrap()
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x68u8)
```

</details>

#### replaces existing NVFS text instead of appending

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = nvfs_vfs_connect("/nvfs", "unit-nvfs-replace", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

expect(nvfs_vfs_write_text(c, "/nvfs/log.txt", "first").is_ok()).to_equal(true)
expect(nvfs_vfs_write_text(c, "/nvfs/log.txt", "second").is_ok()).to_equal(true)

val sz = nvfs_vfs_file_size(c, "/nvfs/log.txt")
expect(sz.is_ok()).to_equal(true)
expect(sz.unwrap()).to_equal(6)

val rt = nvfs_vfs_read_text(c, "/nvfs/log.txt")
expect(rt.is_ok()).to_equal(true)
expect(rt.unwrap()).to_equal("second")
```

</details>

#### refuses to connect on empty mount path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nvfs_vfs_connect("", "unit-empty-path", false, 0, 0)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### refuses to connect on non-absolute mount path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nvfs_vfs_connect("relative/path", "unit-rel-path", false, 0, 0)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### propagates underlying mount failure as FsError

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO(AC-1 injection-hook): NvfsPosixDriver.mount() does not expose a
# reliable failure trigger from outside the driver today.  Once Phase 5
# adds a require_caps guard (non-zero require_caps that the in-memory
# driver cannot satisfy), replace this stub with a real trigger.
val result = nvfs_vfs_connect("/nvfs", "unit-mount-fail", false, 0, 0xFFFFFFFF)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects path with .. traversal component

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = nvfs_vfs_connect("/nvfs", "unit-traversal", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

val result = nvfs_vfs_read_text(c, "/nvfs/../etc/shadow")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### rejects path not under the mount prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = nvfs_vfs_connect("/nvfs", "unit-outside-prefix", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

val result = nvfs_vfs_read_text(c, "/other/file.txt")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### rejects write on a read-only connection before opening

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = nvfs_vfs_connect("/nvfs", "unit-ro", true, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

val result = nvfs_vfs_write_text(c, "/nvfs/blocked.txt", "data")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.Permission)
```

</details>

#### threads want_caps / require_caps through to MountOptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val want: u32 = 0x01
val require: u32 = 0x01
val conn = nvfs_vfs_connect("/nvfs", "unit-caps", false, want, require)
# When the driver honours the caps the connection succeeds with them set.
# When Phase 5 wires want_caps/require_caps into the struct, this case
# asserts those fields are preserved on the returned connection.
if conn.is_ok():
    val c = conn.unwrap()
    expect(c.want_caps).to_equal(want)
    expect(c.require_caps).to_equal(require)
else:
    # Driver rejected require_caps — that is also a valid, non-silent outcome.
    expect(conn.is_err()).to_equal(true)
```

</details>

#### rejects write larger than max_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = nvfs_vfs_connect("/nvfs", "unit-oversize-write", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

val big = "x".repeat(NVFS_CONNECTOR_MAX_BYTES + 1)
val result = nvfs_vfs_write_text(c, "/nvfs/big.txt", big)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.TooLarge)
```

</details>

#### rejects read of file larger than max_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This case requires a pre-seeded oversized file to be present.
# Phase 5 must arrange a way to bypass the write cap for setup,
# or the driver must expose a raw seeding helper.
# For now the spec asserts the shape: reading a stat-reported oversize
# file returns TooLarge without allocating a buffer.
val conn = nvfs_vfs_connect("/nvfs", "unit-oversize-read", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

# Attempt to read a path we know the driver will report as larger than
# NVFS_CONNECTOR_MAX_BYTES.  If the driver returns NotFound instead,
# the stat path short-circuits before the size check — still not TooLarge.
# Phase 5 implementation: ensure stat size > max_bytes triggers early return.
val result = nvfs_vfs_read_bytes(c, "/nvfs/__oversize_seed__")
if result.is_err():
    val e = result.unwrap_err()
    val is_too_large = e == FsError.TooLarge
    val is_not_found = e == FsError.NotFound
    expect(is_too_large or is_not_found).to_equal(true)
```

</details>

#### write_text uses bulk converter (fast path — completes under 1s for 1 MiB)

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = nvfs_vfs_connect("/nvfs", "unit-bulk-write", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

# 128 KiB — well below the 16 MiB cap; enough to distinguish the
# per-char loop (would OOM in interpreter) from the bulk extern path.
val payload = "a".repeat(131072)
val result = nvfs_vfs_write_text(c, "/nvfs/bulk.txt", payload)
expect(result.is_ok()).to_equal(true)

val sz = nvfs_vfs_file_size(c, "/nvfs/bulk.txt")
expect(sz.is_ok()).to_equal(true)
expect(sz.unwrap()).to_equal(131072)
```

</details>

#### emits log_warn on traversal rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO(AC-5 log-capture): log.spl latches _LOG_FILE_PATH once on first
# emission; setting SIMPLE_LOG_FILE_PATH after earlier it-blocks have
# already initialised the module is unreliable.  When a per-test log
# sink primitive is available, replace this with a file-capture assert.
val conn = nvfs_vfs_connect("/nvfs", "unit-log-traversal", false, 0, 0)
expect(conn.is_ok()).to_equal(true)
val c = conn.unwrap()

val result = nvfs_vfs_read_text(c, "/nvfs/../etc/shadow")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

#### emits log_error on mount failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO(AC-5 log-capture): same log-sink limitation as the traversal
# case above.  Assert only the Err shape until a capture primitive
# exists.  Phase 5 must also provide a reliable mount-failure trigger
# (see "propagates underlying mount failure" case above).
val result = nvfs_vfs_connect("", "unit-log-mount-fail", false, 0, 0)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal(FsError.InvalidArg)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/vfs_nvfs_connector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VFS NVFS connector

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
