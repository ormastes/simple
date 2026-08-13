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
