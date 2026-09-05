# SimpleOS x86_64 filesystem execution provider blocker — 2026-08-21

The x86_64 QEMU filesystem-execution boot lane is blocked at the shared
authenticated loader boundary, not at NVMe, FAT32 enumeration, PMM, VMM, TSS,
or ring-3 architecture setup.

`x86_64_fs_exec_spawn_scheduler_owned` intentionally delegates to the shared
path-only gate, which returns `-13`. The loader authority registry keeps token
minting package-private and the admission pipeline currently reports
`CryptographicVerifierUnavailable`. The x86 lane must not recreate authority
from a path, resident bytes, a FAT stream, kernel caller identity, or a QEMU
fixture.

The boot entry now emits the deterministic diagnostic
`X86_64_FS_EXEC_BLOCKED reason=authenticated-provider-unavailable rc=-13`
before its existing `TEST FAILED` result. The positive QEMU gate continues to
require `FS_PROGRAM_END rc=37 reaped=true` and `TEST PASSED`, so this diagnostic
does not turn a blocked boot into false completion evidence.

Unblocking requires the shared loader service to provide a cryptographically
verified image handle, loader-issued authority token, bounded load consumer,
and entry point to `fs_exec_adopt_authenticated_v1`. Once that owner exists,
the x86 boot lane may consume it through the frozen shared interface; no
x86-specific mint or raw-image bypass is permitted.
