# ARM64 raw DTB handoff fixture and hazard review

Date: 2026-11-03. Owner: `/root/bug_db_lead/arm64_native`. No production files edited.

## Exact sources and interface

Reviewed baseline `examples/09_embedded/simple_os/arch/arm64/boot/crt0.S`, SHA256 `082a6021285021e4e3d62ab4422d3a0d0c5bae1056b6889512faa5441ef10534`. Exact proposed candidate from `/tmp/arm64-pci-handoff-candidate-20261103`, SHA256 `07efb6d022d2a4141542c8197c7dd2fe76475f30104607a3fe15ec4d0a519c2b`.

Proposed ABI: `rt_arm64_boot_dtb_address() -> u64`, represented in C as `unsigned long long rt_arm64_boot_dtb_address(void)`. It returns the UNTRUSTED original x0 scalar; zero means absent. Nonzero is neither a valid-memory guarantee nor parsed FDT/PCI admission.

## Actual object evidence

Installed Clang 23.1.0 assembled the entire unchanged baseline and exact proposed crt0 using `--target=aarch64-none-elf -c`. Candidate object and complete `llvm-objdump -dr`/`llvm-readobj --file-headers --sections --relocations --symbols` output are retained in `arm64-dtb-fixture/` beside this report.

- The 64-byte Linux Image header is preserved. `mov x20,x0` is the first instruction at offset `0x40`, before either relocation branch or UART call.
- Header NOP/B does not alter x0. Early logger uses x0/x1/w2; relocation setup uses x9..x17, trampoline x2..x5; early EL setup uses x0/x1. No intervening x20 write was found in this startup path.
- Publication appears after BSS loop termination, `str x20,[x9]` at candidate entry offset `0x19c`, before later logging/C entry.
- `.bss.boot_handoff` is writable allocated NOBITS, size 8, alignment 8. Both current ARM64 linker scripts collect `.bss*`, so BSS clear includes the slot; publication must follow clear.
- Getter is an exported 16-byte AArch64 function: ADRP, ADD, 64-bit LDR into x0, RET. Paired page/low12 relocations target `.bss.boot_handoff`; the scalar is not truncated. x20 is callee-saved under the C calling convention, but after publication the getter depends on the stored slot, not a caller retaining x20.

## Executed reduced fixture

Parent authorized a bounded user-mode fixture, not a system QEMU boot. `handoff-exact.S` copies the actual candidate publication/getter blocks and the actual production relocation data-copy/BSS loops. The synthetic source starts 16 bytes above the destination so a 64-byte ascending copy genuinely overlaps. The fixture copies its trampoline to a deliberately RWX scratch segment and executes it. A C function calls the exported getter, checks the full `0xfedcba9876543210` sentinel, checks eight copied words and checks cleared BSS.

The EL0 fixture omits privileged cache maintenance (DSB/IC IALLU/ISB), EL1/EL2 transitions, UART MMIO, vector setup and real physical firmware placement. It uses Linux process SP and a synthetic image. Thus these are instruction/data/ABI unit results, never firmware/native-platform or PCI acceptance.

Exact-candidate runs (each timeout 1 second):

| Fixture | Expected/actual exit | Time | Meaning |
|---|---|---|---|
| handoff-exact.elf | 0 / 0 | 0.0054 s | Overlapping relocated path preserves scalar through BSS and C getter. |
| handoff-exact-direct.elf | 0 / 0 | 0.0076 s | No-relocation branch preserves scalar through BSS and C getter. |
| handoff-exact-no-save.elf | 11 / 11 | 0.0073 s | Removing original x0 save is detected. |
| handoff-exact-early-publish.elf | 11 / 11 | 0.0073 s | Publishing before BSS and omitting post-clear store is detected. |

All captured stdout/stderr were empty; exit checks are from the actual C comparison. Initial equivalent-proposal controls are retained separately in `results.txt`; they are not counted as additional candidate acceptance. No passing check was rerun without changed candidate code.

## Memory ownership hazards and constraints

1. **Raw pointer preservation is insufficient.** Image-copy destination, scratch writes, BSS clear, downward stack, and future heap writes can overwrite the pointed-to DTB bytes while x20 retains a plausible address. Do not dereference the getter in PCI discovery until a checked memory owner validates and reserves/copies the blob.
2. **Validate before the first destructive operation.** A range check after `.Lbss_done` cannot recover an already-overwritten DTB. Early validation must first establish that the fixed-size FDT header is accessible in admitted RAM, then check magic and big-endian totalsize with overflow-safe bounds, before trusting any blob extent. Null, misalignment, size overflow, unowned memory and overlap must fail closed. This fixture does not implement those checks.
3. **Destination footprint:** overlap policy must cover final `[_start,_kernel_end)`, not merely `[_start,_kernel_load_end)`. `baremetal_stubs.c` has a 512 MiB C `_heap` array in BSS, while linker scripts reserve an additional 8 MiB stack and 64 MiB heap. The active linked map and actual runtime owner determine the complete occupied range; do not infer a 64 MiB-only heap.
4. **Relocation source and scratch:** retain source `[actual_load,actual_load+roundup(load_bytes,8))` and destination ranges. Scratch starts at `(actual_load+rounded_load_bytes+4096)&~15`, then writes a trampoline rounded to 8-byte copies. It is not inherently firmware-reserved RAM; check end arithmetic, actual RAM ownership and DTB/non-kernel overlap. Its address is not rounded up to a page. Copy lengths may write up to 7 bytes beyond the unrounded loaded span.
5. **Copy direction restriction:** current ascending copy is overlap-safe only for destination below source (or disjoint ranges). The main linker base is RAM origin `0x40000000`, but `fs_exec_linker.ld` uses `0x40200000`; a firmware load below that custom link base contradicts the general comment that link base is always lowest. The raw handoff patch does not repair or qualify this existing load-placement restriction.
6. **Initialization timing:** store belongs after BSS clear and before `_c_start`. Putting the slot in BSS and storing at initial entry loses it; storing through a link-absolute data address before relocation can target the wrong image. Register preservation avoids both hazards.
7. **Unowned state:** no setter, public mutable global, cached FDT parse, ECU/PCI-ready marker or speculative pointer dereference is introduced by this ABI. PCI capability activation remains dependent on the later checked owner.

## Reproduction artifacts

Directory: `/tmp/parallel-three-tracks-20261103/bugs/arm64-dtb-fixture/`. Source: `handoff-exact.S`, `checker.c`, `fixture.ld`. Evidence: `results.txt`, `crt0-candidate.o`, `crt0-candidate-disassembly.txt`, `crt0-candidate-object.txt`, `candidate-source.sha256`, `object-checks.txt`. Assembly/link uses `clang --target=aarch64-linux-gnu` and `ld.lld -T fixture.ld`; C uses `-ffreestanding -fno-stack-protector -fno-builtin -O1`. Each linked fixture executes only under `qemu-aarch64` with Python-enforced 1-second timeout.

No full firmware boot, DTB-byte survival, Simple compiler acceptance, ARM64 desktop readiness, or PCI enumeration is claimed. The earlier float candidate remains independently unlanded pending admitted compiler execution.

## Reproducible repository checker and zero case

Prepared `scripts/check/check-arm64-boot-dtb-handoff.py` in the PCI handoff candidate worktree. It extracts the actual candidate save/publication/getter and actual relocation/BSS loops; refuses a clobber before save or any later early-boot x20 use, assembles full production crt0, and generates the reduced fixture with SDN evidence. It refuses existing evidence directories and enforces 1-second emulator timeouts. Invocation: `python3 scripts/check/check-arm64-boot-dtb-handoff.py --output /tmp/<fresh-owned-evidence-directory>`.

Checker syntax was validated with Python AST parsing; generated baseline fixture matches the already-executed exact fixture modulo assembly whitespace, and C/linker inputs match byte-for-byte. Source-order negative controls (inject x0 clobber before save; inject x20 clobber during EL setup) both reject. The packaged whole runner was not reexecuted, to preserve prior green checks; its generated inputs match retained actual execution evidence.

Added a NEW zero raw-input fixture only: `handoff-zero.elf` exited 0 in 0.0059s, proving absent/zero survives relocation/BSS/getter without dereference. Existing four exact-candidate cases were not rerun. This remains reduced EL0 evidence, not firmware or FDT validity.
