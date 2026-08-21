# Simple compiler from the SimpleOS filesystem

> Live, fail-closed QEMU evidence for a nonce-bound filesystem source,
> interpreter, native compiler output, OS loader execution, and init completion.

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
| Updated | 2026-08-21 |
| Evidence | QEMU serial output |

Run with `SIMPLEOS_SIMPLE_FS_E2E=1`. Set `SIMPLEOS_DISK_IMAGE` to override
`build/os/simpleos_disk.img`. A missing gate, image, boot transcript, or exact
marker fails; this spec has no skip path. `SOSIX_QEMU_NONCE` is mandatory and
the observed hello line must equal `hello-<nonce>` exactly.
The guest init invokes `/usr/bin/simple` for all three toolchain operations.
It re-reads and hashes the written source and compiled executable bytes, then
emits the shared `SOSIX_FS_TOOLCHAIN_*` transaction. The host validator rejects
duplicate begin/version records, stale nonces, digest substitution, reordered
operations, and stdout whose observed bytes do not hash to the expected hello.

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
2. Require the exact nonce-specific hello followed by `TRIVIAL_INTERPRETER_OK`.
3. Require a second exact nonce-specific hello followed by `TRIVIAL_LOADER_OK`.
4. Require the later exact line `TRIVIAL_SELFHOST_OK`.
5. Require the still-later exact line `SIMPLEOS_SMOKE_INIT_DONE`.

<details>
<summary>Executable SSpec</summary>

```simple
step("Reuse the live SimpleOS serial capture")
val serial = ensure_serial()
step("Observe the exact interpreter success marker")
val interpreted_output_line = _line_index_after(serial, _expected_hello_output(), -1)
val interpreter_line = _marker_line_index(serial, MARKER_INTERPRETER)
expect(interpreter_line).to_be_greater_than(interpreted_output_line)
step("Observe the exact native compile-and-run success marker")
val native_output_line = _line_index_after(serial, _expected_hello_output(), interpreter_line)
val loader_line = _marker_line_index(serial, MARKER_LOADER)
expect(loader_line).to_be_greater_than(native_output_line)
val native_line = _marker_line_index(serial, MARKER_NATIVE)
expect(native_line).to_be_greater_than(loader_line)
step("Observe the exact smoke-init completion marker")
expect(_marker_line_index(serial, MARKER_DONE)).to_be_greater_than(native_line)
```

</details>

## Pass Criteria

- The live gate equals `1` and the disk image exists.
- The version marker is an exact serial line after smoke-init starts.
- Both observed hello lines exactly equal `hello-<SOSIX_QEMU_NONCE>`.
- The interpreter, compiler-output, loader, and final transaction records bind
  the same source/executable SHA-256 values and nonce in strict order.
- Native success precedes the exact init completion marker.
- No fixture, prebuilt transcript, substring-only marker, or skip result counts.
