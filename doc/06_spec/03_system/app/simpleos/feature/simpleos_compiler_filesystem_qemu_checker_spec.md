# SimpleOS Compiler-Filesystem QEMU Checker

This operator contract explains the fail-closed evidence gate for launching a
target-native Simple compiler from the SimpleOS filesystem. The executable
spec uses a hermetic fake-QEMU transport and therefore validates only the host
parser, manifest, receipt, and blocker behavior—not a live boot.

## Preconditions

- POSIX `sh` and `sha256sum` are available.
- Live x86_64 is blocked until its runner emits the documented guest markers,
  exposes the exact launched image, and injects the checker nonce.
- AArch64 is intentionally blocked until a truthful live compiler route exists.

## Operator workflow

1. Run the hermetic contract with `--arch=x86_64`, `--image`, a bounded timeout,
   and a retained output directory.
2. Confirm the final status is `contract-pass`; it is not live evidence.
3. Verify the receipt's `manifest_sha256` against the manifest.
4. Retain the serial log, manifest, and receipt together.

## Scenarios

### Complete x86 transcript is hash-bound

Run the checker through fake QEMU, require every filesystem role plus
version/hello markers, bind the exact host image, compiler identity, nonce, and
expected output hash, then independently compare manifest and receipt hashes.

### Adversarial transcripts fail closed

Reject missing roles, malformed or duplicate fields, guest `SKIP`, duplicate
final PASS markers, identity/nonce/output/image mismatches, and runner failure.
Failures invalidate any prior publication.

### Unavailable live producers remain explicit

Requesting x86_64 or AArch64 live evidence exits with blocker status and a
concrete resume condition. Neither silently skips or passes.

## Evidence and limitations

The executable source is
`test/03_system/app/simpleos/feature/simpleos_compiler_filesystem_qemu_checker_spec.spl`.
Fake-QEMU artifacts are labeled `contract-pass` and live under
`build/test-artifacts/simpleos-compiler-filesystem-qemu/`. Only a later live
x86 producer can establish QEMU evidence. Physical Uno-Q evidence remains separate.
