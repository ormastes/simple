# Simple compiler from the SimpleOS filesystem

> Live, fail-closed QEMU evidence for version, interpreter, native compiler,
> native executable, and init completion markers.

Requirement: REQ-005

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active — live gate required |
| Source | `test/03_system/os/e2e/simple_from_fs_spec.spl` |
| Updated | 2026-07-11 |
| Evidence | QEMU serial output |

Run with `SIMPLEOS_SIMPLE_FS_E2E=1`. Set `SIMPLEOS_DISK_IMAGE` to override
`build/os/simpleos_disk.img`. A missing gate, image, boot transcript, or exact
marker fails; this spec has no skip path.
The guest init invokes `/usr/bin/simple` for all three toolchain operations.

## Scenarios

### Require live evidence

1. Require `SIMPLEOS_SIMPLE_FS_E2E=1`.
2. Require the selected SimpleOS disk image.

<details>
<summary>Executable SSpec</summary>

```simple
step("Require SIMPLEOS_SIMPLE_FS_E2E=1")
expect(_gate()).to_equal("1")
step("Require the selected SimpleOS disk image")
expect(file_exists(_disk_image_path())).to_equal(true)
```

</details>

### Run filesystem Simple version

1. Boot the selected image once and capture serial output.
2. Require the exact line `SIMPLEOS_SMOKE_INIT_STARTED`.
3. Require the later exact line `SIMPLE_FROM_FS_VERSION_OK`.

<details>
<summary>Executable SSpec</summary>

```simple
step("Boot the selected SimpleOS disk image once")
val serial = ensure_serial()
step("Observe the exact smoke-init start marker")
val started_line = _marker_line_index(serial, MARKER_STARTED)
expect(started_line).to_be_greater_than(-1)
step("Observe the exact filesystem Simple version marker")
expect(_marker_line_index(serial, MARKER_VERSION)).to_be_greater_than(started_line)
```

</details>

### Interpret, native-build, and run

1. Reuse the live serial capture.
2. Require the exact line `TRIVIAL_INTERPRETER_OK`.
3. Require the later exact line `TRIVIAL_SELFHOST_OK`.
4. Require the still-later exact line `SIMPLEOS_SMOKE_INIT_DONE`.

<details>
<summary>Executable SSpec</summary>

```simple
step("Reuse the live SimpleOS serial capture")
val serial = ensure_serial()
step("Observe the exact interpreter success marker")
val interpreter_line = _marker_line_index(serial, MARKER_INTERPRETER)
expect(interpreter_line).to_be_greater_than(-1)
step("Observe the exact native compile-and-run success marker")
val native_line = _marker_line_index(serial, MARKER_NATIVE)
expect(native_line).to_be_greater_than(interpreter_line)
step("Observe the exact smoke-init completion marker")
expect(_marker_line_index(serial, MARKER_DONE)).to_be_greater_than(native_line)
```

</details>

## Pass Criteria

- The live gate equals `1` and the disk image exists.
- The version marker is an exact serial line after smoke-init starts.
- The interpreter marker is an exact serial line before native success.
- Native success precedes the exact init completion marker.
- No fixture, prebuilt transcript, substring-only marker, or skip result counts.
