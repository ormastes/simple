# SimpleOS Compiler-Filesystem QEMU Checker

This operator contract explains the fail-closed evidence gate for launching a
target-native Simple compiler from the SimpleOS filesystem. The executable
spec uses a hermetic fake-QEMU transport and therefore validates only the host
parser, manifest, receipt, and blocker behavior—not a live boot.

## Preconditions

- POSIX `sh` and `sha256sum` are available.
- Live x86_64 use requires the canonical `x64-desktop-disk` scenario to emit
  the documented guest markers from actual guest execution.
- AArch64 is intentionally blocked until a truthful live compiler route exists.

## Operator workflow

1. Run the checker with `--arch=x86_64`, a bounded timeout, and a retained
   output directory.
2. Confirm the final status is `pass`.
3. Verify the receipt's `manifest_sha256` against the manifest.
4. Retain the serial log, manifest, and receipt together.

## Scenarios

### Complete x86 transcript is hash-bound

Run the checker through fake QEMU, require every filesystem role plus real
version/hello markers, then independently compare the manifest hash to the
receipt.

### Adversarial transcripts fail closed

Reject a missing role, a guest `SKIP`, duplicate final PASS markers, and a
nonzero QEMU runner exit. None may publish passing evidence.

### AArch64 remains explicit

Requesting AArch64 exits with blocker status and a concrete resume condition.
It never silently skips or passes.

## Evidence and limitations

The executable source is
`test/03_system/app/simpleos/feature/simpleos_compiler_filesystem_qemu_checker_spec.spl`.
Fake-QEMU artifacts are labeled `contract-pass` and live under
`build/test-artifacts/simpleos-compiler-filesystem-qemu/`. Only a later live
x86 run can establish QEMU evidence. Physical Uno-Q evidence remains separate.
