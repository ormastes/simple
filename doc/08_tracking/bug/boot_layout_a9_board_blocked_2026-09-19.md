# Boot layout (lane A9): internal-linker rung 3 reached, rung 4 partial (hello kernel boots, gate FAIL by design); board run blocked

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
| 3. `llvm-readelf -l -S` parity: internal engine vs `ld.lld -T` | **PASS** (2026-09-19, lane B1) | See "Rung 3 evidence" |
| 4. Real-firmware QEMU boot with the internally linked kernel | **PARTIAL.** The gate verdict is FAIL (exit 1) for BOTH the internal and the ld.lld kernel, because the hello kernel is not the kernel the gate checks. The internal kernel boots and prints the same serial log as the ld.lld one. | See "Rung 4 evidence" |
| Board boot | **BLOCKED** | This host has no board access |

Rung 1 is not vacuous. `ld_tokens_equivalent` compares the source token stream with the
printed token stream (comments and `;` are ignored), and the spec checks that it fails
when one `AT()` bias is dropped. The parser is fail-closed: an unknown directive is an
`Err`, not a skipped token.

## Rung 3 evidence (2026-09-19, lane B1)

The engine is `src/compiler/70.backend/linker/elf/elf_boot_link.spl` (`elf_boot_link`,
`elf_boot_link_image`, `elf_boot_link_named`). It replays `BootLayoutPlan.ops` in source order.
`BootLayoutPlan` now keeps that order (`ops`, `top_ops`, and a `body` for each section).
`elf_exec_writer` now writes `p_paddr`. Specs:

- `elf_boot_link_spec`: 25 examples. Every expected number comes from ld.lld 23.1.0 (`--no-relax -T`).
- `boot_layout_ops_spec`: 17 examples.

**Objects.** The seed `native-build` from the hello build script was run with
`SIMPLE_BOOTSTRAP=1 SIMPLE_KEEP_NATIVE_OBJS=1 ... --verbose`. This keeps the object directory and
prints the exact `ld.lld` command: 5 objects, 3 `--defsym`, `--gc-sections`.

**Comparison.** The same objects, script and defsyms were linked two ways:

- (a) `ld.lld -O0 --no-relax -T linker_limine.ld`, without `--gc-sections`.
- (b) The internal engine, with `boot_layout_add_defsym` for each defsym. This took 75 s in the
  interpreter.

**Results:**

- **Program headers:** identical.
  - `LOAD` at 0x10000, VMA 0xffffffff80100000, PA 0x40100000, size 0xa83c, `R E`.
  - `LOAD` at 0x1b000, VMA 0xffffffff8010b000, PA 0x4010b000, size 0x3010, `RW`.
  - Both segments have alignment 0x10000.
- **Sections:** `.text`, `.rodata`, `.data`, `.bss` (NOBITS) and `.got` have the same address,
  offset, size and alignment.
- **Entry:** identical.
- **Symbols:** all 359 defined globals have the same value.
- **Bytes:** the file range 0x10000-0x1e010, which covers every loaded byte, is byte-identical.
- **Remaining differences:**
  - `.rodata` `sh_flags` is `A` here and `AMS` in lld.
  - `e_shoff` and the layout of the non-loaded `.symtab` differ. The internal output emits globals
    only.
- **Two lld behaviours matter for byte parity:**
  - GOT slot order. lld orders slots by the symbol table, not by relocation order. The engine now
    does the same.
  - String order. At its default `-O1`, lld reorders the strings of a `SHF_MERGE|SHF_STRINGS`
    input (`.rodata.str1.1`) through its hash-sharded string table. The size is unchanged, but the
    string order and every reference to it differ. So byte parity holds against `-O0`. Against
    lld's default output, only the layout and the symbols match.
- **Not compared:** the `--gc-sections` image that the build ships. The engine has no GC.

## Rung 4 evidence (2026-09-19, lane B1)

The command:

```sh
OUT_DIR=<d> ART_DIR=<d> WORK_DIR=<d>/work KERNEL_ELF=<internally linked kernel.elf> \
AAVMF_CODE=~/.local/share/qemu/edk2-aarch64-code.fd AAVMF_VARS=~/.local/share/qemu/edk2-arm-vars.fd \
  sh scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs
```

The boot chain is EDK2 pflash, then `BOOTAA64.EFI` (Limine), then the internally linked
`kernel.elf`. No `-kernel` was used. The serial log shows:

```
[hello] serial up, invoking the Simple hello-world program
HELLO_NATIVE_SIMPLEOS_AARCH64_OK hello world from Simple
HELLO_NATIVE_SIMPLEOS_AARCH64 second line proves the program kept running
[hello] native program exited rc=0
[hello] parking
```

These lines are identical to the output of the externally linked (`--gc-sections`) kernel on the
same gate.

**Binary identity (re-run after the Fable review).** The hashes below tie each log to its ELF. Each
image's copy inside `esp.img` was located at the ELF magic (offset 1326080) and hashed over the
file's length.

| Kernel | Size | sha256 of the ELF = sha256 of the copy in `esp.img` |
|---|---|---|
| Internal (`elf_boot_link`) | 139752 | `cbca17524b077710c8aa31cfc5ae04b56e3943820098448e9e24071a656e0269` |
| ld.lld (`--gc-sections`) | 73584 | `b1eef582ffca0bfd3a7793334968cd035da42102ca9dc10411c154ab751aa832` |

The two full serial logs are byte-identical (sha256 prefix `ca096ec8f4144032`).
- Logs: `build/os/b1/{int,ext}.serial.log`
- Hashes: `build/os/b1/boot_hashes.txt`
- Gate: the command above, with `BOOT_TIMEOUT=60`, run once for each kernel.
- The ESP images were deleted after the run.
- The logs, the hash file and both ELFs are under `build/`, which is gitignored. They are local
  evidence on this host and are not tracked. The table above is the only committed record of the
  hashes.

**What the gate verdict is, exactly.** `check-simpleos-arm64-efi-real-firmware-boot.shs` exited 1
(`FAIL`) for both kernels:

```
FAIL — aarch64 kernel never printed '[BOOT] Memory map:' under EDK2/AAVMF pflash — boot did not complete
```

The gate requires four markers that only the full SimpleOS kernel prints (`[BOOT] Memory map:`,
`[BOOT] Boot info assembled successfully`, `[BOOT] Handing off to memory layer`,
`SIMPLEOS-AARCH64-LIMINE-KERNEL-OK`). Both runs used the hello kernel, which prints the `[hello]` /
`HELLO_NATIVE_SIMPLEOS_AARCH64_OK` lines instead. So the FAIL is a mismatch between the gate and the
payload. It is not a firmware, Limine, board or linker failure:

- EDK2 started.
- Limine loaded the ELF by its program headers.
- The kernel ran to `[hello] parking`.

The claim this record makes is therefore narrower than "the gate passes": the internally linked
hello kernel produces the same serial log as the ld.lld-linked one under the real-firmware chain.
The gate itself has NOT passed for any internally linked kernel. That needs the full kernel's
objects linked internally, which is still open. No board run was attempted, because there is no
board on this host.

## Rung 4 with the full kernel: BLOCKED upstream (2026-09-19, lane C3)

The full kernel is the one the gate checks. Its build fails before any linker comparison can
start: **the external `ld.lld` link fails too.** So there is no reference ELF, no internal ELF, no
sha256 for either, and no gate verdict. Nothing was substituted and no ELF was faked.

**Producer.** The producer is `scripts/os/build-simpleos-aarch64-limine-kernel.shs`, with entry
`examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl` and script
`examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld`. The same command was run at
`7c875a81067` with objects kept. The seed was
`/home/yoon/dev/simple/src/compiler_rust/target/release/simple`, built 2026-09-06, sha256
`e74d6e3ec00f4c9feac900813016b767fb0d3a3470ee0006d0079b72ce6f8497`.

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_KEEP_NATIVE_OBJS=1 $SEED native-build --backend cranelift --entry-closure \
  --timeout 1200 --entry examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl \
  --target aarch64-unknown-none-elf \
  --linker-script examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld --verbose -o kernel_ext.elf
# Compiled: 14/14 (0 cached, 14 fresh, 0 failed) in 0.2s
# Freestanding unresolved symbol check: 35 unexpected symbol(s)
# Freestanding unresolved precheck deferred to linker: 32 candidate symbol(s)
# Build failed: link failed: ld.lld: error: undefined symbol: rt_arm64_mrs_mpidr_el1
#   >>> referenced by mod_2.o:(os__kernel__arch__arm64__cpu__mrs_mpidr_el1)
# ld.lld: error: undefined symbol: rt_value_u64
#   >>> referenced by mod_10.o:(os__kernel__memory__pmm___pmm_reset_contiguous_registry)
# (plus mmio_disable_test_mode, referenced by mod_6.o:(...limine_aarch64_boot_main))
```

**Object set.** The link uses 17 objects: `_boot_freestanding_runtime.o`, `mod_0.o` … `mod_13.o`,
`_init_all.o` and `_stubs_freestanding.o`. It passes `--entry=_start`, three `--defsym`s
(`_start`, `__simple_entry_start` and `spl_start`, each set to
`examples__09_embedded__simple_os__arch__aarch64__limine_entry___start`), `--gc-sections` and
`-z muldefs`.

**Missing symbols.** With `--gc-sections`, 3 symbols are missing. Without it (`ld.lld -O0
--no-relax`, which is the engine's model), 23 are missing. They fall into three groups:

| Class | Symbols | Owner |
|---|---|---|
| Merge-dropped Simple function | `mmio_disable_test_mode`: imported by `src/os/kernel/boot/limine_boot_aarch64.spl:39`, called at `:532`, defined nowhere. It was last defined at `src/os/kernel/boot/mmio.spl:71` in the first parent of merge `e274cd33719` (2026-08-27), and that merge deleted it | kernel |
| Arm64 system-register externs that the aarch64 freestanding runtime does not define | `rt_arm64_{mrs_currentel,mrs_mpidr_el1,mrs/msr_ttbr0_el1,mrs/msr_ttbr1_el1,msr_tcr_el1,msr_mair_el1,msr_sctlr_el1,msr_vbar_el1,isb,dsb,dmb,wfi,wfe,tlbi_alle1,tlbi_vae1,daif_set,daif_clr}` (from `src/os/kernel/arch/arm64/cpu.spl`) | kernel / freestanding runtime |
| Codegen-emitted hosted runtime API | `rt_value_u64`, `rt_value_as_u64`, `rt_unwrap_or_trap` | freestanding runtime (same class as the `rt_struct_alloc` gap in `arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`) |

**Internal engine on the same inputs.** The same 17 objects, script and defsyms were run through
the Appendix driver (`elf_boot_link_named`, interpreter, 1m55s). The engine returned `Err`, not an
image:

```
bootlink: ERROR undefined symbol: rt_arm64_mrs_currentel; ...; rt_value_u64; rt_value_as_u64; rt_unwrap_or_trap
```

The engine's 23-symbol set is identical to ld.lld's `-O0 --no-relax` set (`diff` is empty). So the
engine does not mask undefined symbols. The engine also relocated every placed input before
reporting the undefined set, and it hit no unsupported relocation or script construct. The
kernel's relocations are 1127 `ABS64`, 680 `CALL26`, 143 `ADR_PREL_PG_HI21`, 140
`ADD_ABS_LO12_NC`, 3 `LDST64_ABS_LO12_NC`, 3 `ADR_GOT_PAGE`, 3 `LD64_GOT_LO12_NC` and 1 `PREL32`.
**No linker work is pending for this kernel.** What blocks it is the missing symbols.

**What unblocks rung 4:**

1. The kernel lane restores `mmio_disable_test_mode`.
2. The kernel lane defines the `rt_arm64_*` externs and `rt_value_u64`, `rt_value_as_u64` and
   `rt_unwrap_or_trap` in `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`.
3. Because the engine has no section GC, all 23 must resolve, not just the 3 reachable ones. The
   other option is to land section GC first.

Then rerun the steps above, and the Rung 4 gate command with `KERNEL_ELF` set to each ELF.
Evidence is local only, in `build/os/c3/` (logs, objects, and both undefined lists).

## Why rung 3 was not reached before lane B1 (historical)

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
2. Done (lane B1): keep objects with `SIMPLE_KEEP_NATIVE_OBJS=1`, and rung-3 parity. Still open:
   - Section GC (KEEP roots), so the engine can match the shipped `--gc-sections` image.
   - lld's `-O1` string-merge order.
   - A committed parity script (`scripts/check/check-boot-layout-parity.shs`) and its CI step.
3. Done (lane B1): rung 4 with the hello kernel. Still open: rung 4 with the full kernel. It is
   blocked upstream because the kernel does not link with ld.lld either (23 undefined symbols).
   See "Rung 4 with the full kernel".
4. Close this record with a board transcript.

## Appendix: reproducing rungs 3-4

Step 1. Build the objects and keep them. Run this from the repo root with the seed at `$SEED`:

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_KEEP_NATIVE_OBJS=1 $SEED native-build --backend cranelift --entry-closure \
  --timeout 1200 --entry examples/09_embedded/simple_os/arch/aarch64/hello_world_efi_entry.spl \
  --target aarch64-unknown-none-elf \
  --linker-script examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld \
  --verbose -o kernel_ext.elf
# The output prints "Keeping native object files in <dir>" and the "Freestanding link command".
```

Step 2. Produce the external reference. This is the same command without `--gc-sections`:

```sh
E=examples__09_embedded__simple_os__arch__aarch64__hello_world_efi_entry___start
ld.lld -O0 --no-relax -T<script> -o ext_O0.elf <dir>/_boot_freestanding_runtime.o <dir>/mod_0.o \
  <dir>/mod_1.o <dir>/_init_all.o <dir>/_stubs_freestanding.o --entry=_start \
  --defsym=_start=$E --defsym=__simple_entry_start=$E --defsym=spl_start=$E
```

Step 3. Produce the internal link. Save the driver below as `bootlink_driver.spl` and run
`bin/simple run bootlink_driver.spl kernel_int.elf <script> aarch64 --defsym=... <objects in the same order>`.

Step 4. Compare the two images. Use `llvm-readelf -l -S -s` and `cmp` over the loaded file range.
Then run rung 4 with the command in "Rung 4 evidence".

```simple
# usage: bin/simple run bootlink_driver.spl <out> <script> <arch> [--defsym=a=b ...] obj...
use compiler.backend.linker.elf.elf_boot_link.{elf_boot_link_named}
use compiler.backend.linker.boot_layout.boot_layout_plan.{boot_layout_from_text, boot_layout_add_defsym}
use compiler.backend.linker.reloc_engine.{RelocArch}
use std.io_runtime.{file_read, file_read_bytes, file_write_bytes, sys_get_args}

fn main():
    val args = sys_get_args()
    var i: i64 = 0
    while i < args.len() and not args[i].ends_with("bootlink_driver.spl"):
        i = i + 1
    val out = args[i + 1]
    val script = args[i + 2]
    val arch = args[i + 3]
    var plan = boot_layout_from_text(file_read(script)).unwrap()
    var objs: [[i64]] = []
    var names: [text] = []
    var j = i + 4
    while j < args.len():
        val a = args[j]
        if a.starts_with("--defsym="):
            val kv = a[9:]
            var eq: i64 = 0
            while kv[eq:eq + 1] != "=":
                eq = eq + 1
            plan = boot_layout_add_defsym(plan, kv[0:eq], kv[eq + 1:])
        else:
            val raw = file_read_bytes(a)
            var o: [i64] = []
            var k: i64 = 0
            while k < raw.len():
                o = o.push(raw[k] as i64)
                k = k + 1
            objs = objs.push(o)
            names = names.push(a)
        j = j + 1
    val target = if arch == "x86_64": RelocArch.X86_64 else: RelocArch.AArch64
    match elf_boot_link_named(objs, names, plan, target):
        case Ok(im):
            var b: [u8] = []
            for x in im.bytes:
                b = b.push(x as u8)
            file_write_bytes(out, b)
            print "bootlink: wrote {out} ({im.bytes.len()} bytes)"
        case Err(e):
            print "bootlink: ERROR {e}"
```
