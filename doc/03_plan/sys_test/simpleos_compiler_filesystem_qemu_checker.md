# SimpleOS Compiler-Filesystem QEMU Checker Test Plan

## Scope

This plan qualifies the host checker contract for future live SimpleOS x86_64
serial evidence from a filesystem-installed target-native Simple compiler. It checks
argument handling, exact/unique markers, all required filesystem roles,
in-guest version and compile/run evidence, SHA-256 binding, atomic manifest and
receipt publication, and fail-closed behavior.

The hermetic tests emit `contract-pass`, never `pass`, and do not claim a live
QEMU boot. Both live architectures remain blocked: x86_64 lacks a guest marker
producer that exposes the launched image identity and nonce, while AArch64 also
lacks its target-native payload and in-guest exec route.

## Acceptance and execution

1. Run `test/03_system/app/simpleos/feature/simpleos_compiler_filesystem_qemu_checker_spec.spl`.
2. The live x86_64 command currently exits 3 with
   `x86-live-marker-producer-unavailable`; this is a blocker, not evidence.
3. A future live pass requires exactly one begin/version/hello/pass marker, exactly
   one marker for every required role, no fail/skip marker, and a receipt whose
   SHA-256 matches the atomically published manifest.
4. `--arch=aarch64` must exit 3 with the explicit live-route blocker; it must
   never skip or pass.

## Traceability

| Requirement | Evidence | Cases | Coverage |
|---|---|---:|---|
| REQ-SOS-CFS-QEMU-001 | `test/03_system/app/simpleos/feature/simpleos_compiler_filesystem_qemu_checker_spec.spl` and mirrored manual | 1 | Complete host contract; live boot blocked |
| REQ-SOS-CFS-QEMU-002 | Same spec, adversarial fake-QEMU matrix and stale-output case | 11 | Complete |
| REQ-SOS-CFS-QEMU-003 | Same spec, x86_64 and AArch64 blocker scenarios | 2 | Complete blocker honesty |

## Risks and evidence policy

- Marker text alone is insufficient: marker uniqueness, launched host image,
  compiler-role identity, nonce, and expected hello-output hash are checked.
- Host `bin/simple`, fixed-command QEMU responses, `SKIP`, and host-side
  compilation are rejected.
- Fake-QEMU output is protocol evidence only and is labeled as such.
- The three primary scenarios remain visible in the manual; executable source
  is folded. Captured logs and manifests are linked artifacts, not embedded.
