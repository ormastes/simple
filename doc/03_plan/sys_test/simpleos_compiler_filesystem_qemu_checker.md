# SimpleOS Compiler-Filesystem QEMU Checker Test Plan

## Scope

This plan qualifies the host checker that accepts live SimpleOS x86_64 serial
evidence for a filesystem-installed target-native Simple compiler. It checks
argument handling, exact/unique markers, all required filesystem roles,
in-guest version and compile/run evidence, SHA-256 binding, atomic manifest and
receipt publication, and fail-closed behavior.

The hermetic tests emit `contract-pass`, never `pass`, and do not claim a live QEMU boot. AArch64 remains blocked until
its target-native payload and in-guest exec route exist.

## Acceptance and execution

1. Run `test/03_system/app/simpleos/feature/simpleos_compiler_filesystem_qemu_checker_spec.spl`.
2. For live x86_64 evidence run `sh scripts/check/check-simpleos-compiler-filesystem-qemu.shs --arch=x86_64 --timeout=180 --output-dir=build/test-artifacts/simpleos-compiler-filesystem-qemu/live`.
3. A live pass requires exactly one begin/version/hello/pass marker, exactly
   one marker for every required role, no fail/skip marker, and a receipt whose
   SHA-256 matches the atomically published manifest.
4. `--arch=aarch64` must exit 3 with the explicit live-route blocker; it must
   never skip or pass.

## Traceability

| Requirement | Evidence | Cases | Coverage |
|---|---|---:|---|
| REQ-SOS-CFS-QEMU-001 | `test/03_system/app/simpleos/feature/simpleos_compiler_filesystem_qemu_checker_spec.spl` and mirrored manual | 1 | Complete host contract; live boot separate |
| REQ-SOS-CFS-QEMU-002 | Same spec, adversarial fake-QEMU matrix | 4 | Complete |
| REQ-SOS-CFS-QEMU-003 | Same spec, AArch64 blocker scenario | 1 | Complete blocker honesty |

## Risks and evidence policy

- Marker text alone is insufficient: marker uniqueness and hashes are checked.
- Host `bin/simple`, fixed-command QEMU responses, `SKIP`, and host-side
  compilation are rejected.
- Fake-QEMU output is protocol evidence only and is labeled as such.
- The three primary scenarios remain visible in the manual; executable source
  is folded. Captured logs and manifests are linked artifacts, not embedded.
