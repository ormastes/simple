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
`x86_64-unknown-simpleos` simple-core archive, imports only the required native
port-I/O primitive, adds board-owned freestanding runtime and serial providers,
includes the existing Multiboot CRT, and invokes native-build with
`--runtime-bundle simple-core` and stub fallback disabled.
The admitted Stage 3 compiler produced a 68,936-byte x86-64 ELF, which was
packaged into a 256 MiB GPT/FAT32 removable UEFI image. The structural checker
passed seven GPT/ESP/BOOTX64 checks. Physical F7 boot remains a separate live
criterion.

The later hosted-syscall retention defect is distinct and tracked in
`up2_ring0_hosted_syscall_closure_2026-08-20.md`.

Resume command after changing the provider contract:

```text
SIMPLE_BUILD_COMPILER=/home/yoon/simple/build/bootstrap-stage23-sync-final/stage3/x86_64-unknown-linux-gnu/simple sh scripts/os/build-simpleos-up-squared-apollo-lake.shs
```
