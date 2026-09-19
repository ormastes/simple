# Boot layout (lane A9): internal-linker boot rungs 3-4 not reached; board run blocked

Status: OPEN (P2)
**Date:** 2026-09-19
**Owner:** lane A9, mold/MDSOC++ linker plan
**Related:** `doc/03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md` (A9 row, gate G4),
`doc/05_design/compiler/linker/mold_mdsocpp_linker_design.md` §9, `.claude/rules/board-runnable.md`

## Rungs reached

| Rung (design §9) | State | Evidence |
|---|---|---|
| 1. `ld_parse` round-trips all 6 `src/os/kernel/arch/*/linker.ld` | **PASS** | `test/01_unit/compiler/backend/linker/linker_script_spec.spl` 44/44. Before this change: 31 pass, 12 fail (PHDRS, AT, KEEP, NOLOAD, `+=`, OUTPUT_FORMAT, PROVIDE, ASSERT, round-trip) |
| 2. Typed `BootLayoutPlan` | **PASS** | `test/01_unit/compiler/backend/linker/boot_layout_plan_spec.spl` 22/22, with values worked out by hand for x86_64 (higher half) and arm64 (MEMORY/NOLOAD). A mutation run flipped 3 expectations and all 3 went red |
| 3. `llvm-readelf -l -S` parity: internal engine vs `ld.lld -T` | **NOT REACHED** (not blocked) | See below |
| 4. Real-firmware QEMU boot with the internally linked kernel | **NOT REACHED** (depends on rung 3) | See below |
| Board boot | **BLOCKED** | This host has no board access |

Rung 1 is not vacuous. `ld_tokens_equivalent` compares the source token stream with the
printed token stream (comments and `;` are ignored), and the spec checks that it fails
when one `AT()` bias is dropped. The parser is fail-closed: an unknown directive is an
`Err`, not a skipped token.

## Why rung 3 is not reached

This is unimplemented engine work. It is not a tooling block. The internal ELF engine
(`src/compiler/70.backend/linker/elf/elf_static_link.spl` and `elf_exec_writer.spl`) does
not support any of the following:

- A caller-chosen base address. The base is fixed at `ELF_STATIC_BASE = 0x400000`.
- Per-output-section VMA or LMA.
- MEMORY regions.
- PHDRS-driven segments. It always emits R, RX and RW `PT_LOAD` segments plus `GNU_STACK`, from 4 flag-kinds.
- NOLOAD, `. +=` padding, or symbol assignment.

`BootLayoutPlan` carries all of these as typed data, so that engine can take it as input.

Kernel objects **can** be produced on this host (aarch64). On 2026-09-19,
`SIMPLE_BOOTSTRAP=1 sh scripts/os/build-simpleos-aarch64-hello-kernel.shs` built a 73,584-byte
kernel in about 0.2 s with the Rust seed. Two limits apply:

- The native-build link deletes its intermediate objects (`simpleos_native_linkers.spl:67-70`). A rung-3 run needs a keep-objects path, or a relink from those objects.
- Correction (Fable review, 2026-09-19): `src/os/kernel/arch/arm64/linker.ld` **is** consumed. `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl:44,57` declares it as the arm64 platform target's linker script, and the Simple-side build path reads it from there (`src/os/port/simpleos_native_build_config.spl`, `src/os/qemu_runner_part2.spl`, which passes it to the link and checks it for staleness). The *shell* gates use `examples/` scripts instead:
  - `scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs`, through `scripts/os/build-simpleos-aarch64-*-kernel.shs`, uses `examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld`.
  - The `simpleos_native_linkers.spl:75` default, used when `SIMPLE_NATIVE_BUILD_LINKER_SCRIPT` is unset, is `examples/09_embedded/simple_os/arch/arm64/linker.ld`.

  So a rung-4 substitution through the EFI gate exercises the `examples` Limine script, not the `src/os` one. Every in-tree `.ld` file (50 of them, from `git ls-files '*.ld'`) parses and prints token-equivalent. `linker_script_spec` checks this.

## Real-firmware proxy state on this host (baseline, external linker)

- Firmware: `~/.local/share/qemu/edk2-aarch64-code.fd` (CODE) and `~/.local/share/qemu/edk2-arm-vars.fd` (VARS). There is nothing under `/usr/share/AAVMF`. The gate fails with "no AAVMF_VARS.fd found" unless `AAVMF_VARS` is set.
- `vendor/limine/BOOTAA64.EFI` is present.
- The command below booted the externally linked (clang/lld) hello kernel under EDK2 pflash, then BOOTAA64.EFI (Limine), then `kernel.elf`, and printed `HELLO_NATIVE_SIMPLEOS_AARCH64_OK hello world from Simple`:

  ```sh
  KERNEL_ELF=<hello kernel.elf> \
  AAVMF_CODE=~/.local/share/qemu/edk2-aarch64-code.fd \
  AAVMF_VARS=~/.local/share/qemu/edk2-arm-vars.fd \
  sh scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs
  ```

  The gate still reports FAIL, because it waits for the full kernel's `[BOOT] Memory map:` markers. The hello kernel does not print them. So the proxy path works on this host, but the gate needs the full-kernel ELF.

## What a board run needs

- A physical aarch64 board with UEFI (EDK2) firmware, and x86_64 hardware with UEFI for the higher-half script.
- Board identity, the download or boot path (the same ESP: `BOOTAA64.EFI` + `limine.conf` + `kernel.elf`), and a serial or SSH transcript showing the same boot markers the QEMU gate checks.
- The external `-T` linker stays the producer until that transcript exists (design §9).

## Next steps

1. Extend the ELF engine to honour a `BootLayoutPlan`:
   - VMA/LMA per section from `boot_eval`
   - PHDRS or region placement
   - NOLOAD sections as `SHT_NOBITS`
   - KEEP globs as `--gc-sections` roots
   - symbol assignment
2. Add a keep-objects path to the SimpleOS native link, then compare `llvm-readelf -l -S` against `ld.lld -T` on the same objects (rung 3).
3. Substitute the internally linked kernel via `KERNEL_ELF=` in the EFI gate (rung 4).
4. Close this record with a board transcript.
