# SOSIX/QEMU Guest Filesystem Evidence Contract

## Purpose

This contract prevents a QEMU row from passing on boot markers alone. A valid row must correlate host, guest, and a fresh nonce across boot, filesystem mount, directory listing, and one target-native program loaded from the guest filesystem.

## Primary flow

1. **Load the canonical QEMU settings.** Resolve host, emulator, accelerator, and configured artifact root.
2. **Prepare isolated guest media.** Bind the kernel and filesystem image to the retained run identity.
3. **Boot the requested host and guest row.** Capture a nonce-correlated `SOSIX_QEMU_BOOT PASS` marker.
4. **Inspect the mounted filesystem.** Require mount, listing begin, expected entry, and listing end markers with the same identity.
5. **Run an arbitrary filesystem program.** Require its path, expected stdout, zero exit, and target-native provenance with the same nonce.
6. **Retain the correlated evidence bundle.** Preserve settings, argv, hashes, transcript, status, and reason.

## Failure policy

The classifier blocks missing host/guest identity, boot, mount, listing, expected entry, program path/nonce/output, zero exit, and target-native provenance. It also rejects explicit fixed responses and listing markers replayed from another nonce.

This unit contract is necessary but not sufficient for a platform PASS. Per-architecture system scenarios must populate it from a retained production guest transcript. Host-side `ls`, fixed SSH/QEMU replies, source strings, and artifact presence do not satisfy the contract.

## Executable source

`test/01_unit/os/sosix/qemu_guest_filesystem_receipt_spec.spl`

Current diagnostic result: 7 examples executed, 7 passed, 0 failed, 0 dropped. The deployed binary identified itself as a Rust bootstrap seed, so this result is diagnostic pending rerun on a current pure-Simple Stage 4 CLI.

