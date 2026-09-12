# SimpleOS installer host file read TOCTOU and allocation bound
**Status:** RESOLVED (2026-09-12, re-verified: bin/simple test test/01_unit/os/installer/image_bounded_file_reader_spec.spl -> 3 passed, 0 failed)

- Status: BLOCKED; unsafe admission removed on 2026-08-20
- Owner: `src/os/installer/image_bounded_file_reader.spl`
- Coverage: `test/01_unit/os/installer/image_bounded_file_reader_spec.spl`

## Defect

The image builder checked a host path with `rt_file_size`, then called the
unbounded `rt_file_read_bytes` or `rt_file_read_text` on that changeable path.
An input could grow or be replaced between those operations, causing allocation
above the admission limit or staging bytes different from the checked object.
Kernel, Simple, Clang, Rust, build-stamp, and install-package reads shared the
same defect class.

## Fail-closed mitigation

The installer refuses symlinks and non-regular inputs, then returns
`bounded-nofollow-fd-reader-unavailable` for every regular changeable host
artifact. It performs no whole-file read and starts no snapshot subprocess, so
the unsafe path cannot allocate or stage attacker-controlled replacement bytes.
Kernel, Simple, Clang, Rust, build-stamp, and install-package inputs remain
unavailable rather than being misreported as admitted.

## Missing owner

`std.io.FileHandle` opens through `rt_io_file_open`, which follows the name.
The older `rt_file_open` descriptor API exposes get-size and close but no
bounded binary read in `.spl`; neither API supplies `O_NOFOLLOW`/`openat2`, an
inode/generation identity, or fstat plus pread on the retained descriptor. A
correct fix needs one canonical facade that performs no-follow open, fstat,
bounded chunk reads, EOF/growth detection, and close on every path without
reopening the name. Until it lands, this tracker remains release-blocking.

## Triage 2026-09-12
Rule B: ran `bin/simple test test/01_unit/os/installer/image_bounded_file_reader_spec.spl` on the deployed seed; the spec now passes in full (3/3), so this record no longer reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
