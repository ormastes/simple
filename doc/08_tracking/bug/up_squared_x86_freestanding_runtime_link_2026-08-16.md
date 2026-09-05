# UP Squared minimal x86 freestanding runtime link failure

Status: RESOLVED (2026-08-20)
Owner: UP Squared Apollo Lake SimpleOS lane
Date: 2026-08-16

The provenance-admitted Stage 3 compiler lowers the partial UP2 entry closure,
but the dedicated minimal linker invocation omits the established x86
freestanding runtime bundle. Linker diagnostics include `rt_string_new_literal`,
`rt_for_iterable`, `rt_array_new`, `rt_enum_new`, `serial_println`, and
`rt_serial_readline`.

The fix must bind the canonical x86 C/ASM runtime providers used by existing
SimpleOS board builds. Do not add weak fabricated stubs or use the Rust seed.
After the third bounded cycle the lane stopped per the runaway guard.

Resolution: `build-simpleos-up-squared-apollo-lake.shs` now builds the admitted
`x86_64-unknown-none` simple-core capsule, imports only the required native
port-I/O primitive, adds board-owned freestanding runtime and serial providers,
and emits the Simple closure as an archive. The wrapper directly links that
archive with the existing Multiboot CRT and the board linker script, with stub
fallback disabled. The admitted Stage 3 compiler produced a 37,280-byte
x86-64 ELF and a 256 MiB GPT/FAT32 removable UEFI image. The structural checker
and OVMF boot/`ls /` gate pass. Physical F7 boot remains a separate live
criterion.

The later hosted-syscall retention defect is distinct and tracked in
`up2_ring0_hosted_syscall_closure_2026-08-20.md`.

Resume command after changing the provider contract:

```text
SIMPLE_BUILD_COMPILER=/home/yoon/simple/build/bootstrap-stage23-sync-final/stage3/x86_64-unknown-linux-gnu/simple sh scripts/os/build-simpleos-up-squared-apollo-lake.shs
```
