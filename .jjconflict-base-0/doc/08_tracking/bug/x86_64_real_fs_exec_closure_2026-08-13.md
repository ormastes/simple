# x86_64 real filesystem-exec closure — 2026-08-13

## Functional diagnostic result

The isolated clean lineage reached the complete x86_64 workload lifecycle in
one OVMF/Q35 boot. This is diagnostic evidence only; it is not a 24-row matrix
promotion or a collector bundle.

| Item | Evidence |
| --- | --- |
| Isolated source head | `6a0f5a614b9` |
| Admitted compiler SHA-256 | `23513399e970cfc1c850484c6d75bde7aebe47446835da19f7387c83c6672dd7` |
| Kernel SHA-256 | `270d03b0daa7f94480890ce4bdda38e5da0b602e063eefc5421853ca5a2ed0c0` |
| Serial SHA-256 | `b973331238eeeaee78c48af3c52e11def3c6d32a12fe99d126a985f5ef2c796a` |
| Serial transcript | `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_64-6a0f5a6-v14-20260813/serial.log` |

The transcript proves, in order: kernel nonce media read, ten real
`/SYS/APPS` entries and `FS_LS_END status=pass`, mounted `/FSEXEC.ELF`, target
produced `SIMPLEOS_FS_EXEC_OK`, exit status 37, exact scheduler reap, and final
`FS_PROGRAM_END rc=37 reaped=true` / `TEST PASSED`.

## Repairs that made the result possible

1. `vmm_copy_bytes_to_phys` decodes boxed x86_64 `[u8]` elements rather than
   memcpying their RuntimeValue backing storage into PT_LOAD pages.
2. The bootstrap collector permits only a named PID-0 synthetic-child request,
   not wildcard collection.
3. Reaping uses the task-owned physical root and avoids the freestanding
   nested value-struct receiver trap in isolation metadata.
4. The bootstrap child remains parentless; the exact-child collector rule
   avoids unwrapping a value `TaskId` as a heap receiver.

## Remaining matrix status

This row is not collector-promoted. Canonical 24-row completion still requires
valid evidence bundles for the remaining rows and their firmware/admission
contracts.

## Canonical nonce-separation replay

Commit `6ea9d38c4d0` adds a second, fixed `SOSIXNON.TXT` media slot and keeps
it separate from the workload challenge in `QEMUNONC.TXT`.  The nonce-media
preparer now accepts an optional fourth collector nonce argument and patches
both slots with exact readback.  The x86_64 entry fails closed unless it can
read and validate the collector slot, emits its labeled collector nonce exactly
once, then emits `guest-entry`, and only afterward reads the workload nonce.

One clean admitted rebuild and one OVMF/Q35 boot prove the following order:

1. `SOSIX_COLLECTOR_RUN_NONCE=X86_64_COLLECTOR_NONCE_20260813`
2. `guest-entry`
3. `SIMPLEOS_QEMU_NONCE=X86_64_WORKLOAD_NONCE_20260813`
4. ten real `/SYS/APPS` entries, mounted `/FSEXEC.ELF`, target output, exit
   37, exact reap, and `TEST PASSED`.

| Item | Evidence |
| --- | --- |
| Isolated source head | `6ea9d38c4d0` |
| Admitted compiler SHA-256 | `23513399e970cfc1c850484c6d75bde7aebe47446835da19f7387c83c6672dd7` |
| Kernel SHA-256 | `a9df52f13cb071ca3beecc138ee068d0cf903ac21472b52181c0b7aa652ab833` |
| Base image SHA-256 | `836824dd8715001985ae330475b52dffccf58c1b14e22a1524c0456d7fddb382` |
| Patched image SHA-256 | `20df69cade68a140abc60e70a3ab4830f6afb8865ada6de84319f3a5b0ee6141` |
| Transcript | `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_64-canonical-nonce-20260813/ovmf-check/serial.log` |

At this earlier point the launch was functional evidence only: it lacked the
producer's closed firmware-stage admission. It was not mislabeled as
`direct-kernel`; the subsequent section records the separate canonical replay.

## Canonical OVMF bundle

The v2 evidence schema now admits the literal OVMF/GRUB profile
`BdsDxe: starting Boot>[grub-uefi] multiboot loading>guest-entry`, preserving
the actual firmware and bootloader text rather than inventing generic labels.
From clean source `49db401660aa3aac7b2439ce45a1a73d0e8b5876`, a new pre-admitted
TCG run produced a canonical nine-artifact Linux/x86_64 UEFI-pflash bundle:

`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_64-ovmf-canonical-20260813-final/canonical-root/linux/x86_64/run-X86_64_COLLECTOR_NONCE_20260813_V3/evidence.env`

The evidence record SHA-256 is
`d812a871aa5764fd2e099209862b25e6252490cc99c304ac09bb2f3c7031ec03`.
It binds OVMF file SHA-256, package version `2024.02-2ubuntu0.8`, pre-run host
admission, one-line QEMU argv/version, collector nonce once, workload nonce
twice (kernel and child), the mounted program, and the full exit-37/reap/PASS
lifecycle. The collector was invoked and correctly stopped with `expected
exactly 24 evidence bundles`; this is a row PASS, not a false matrix promotion.
