#!/usr/bin/env python3
"""Check ARM64 raw DTB handoff with a reduced EL0 assembly/C fixture.

Assembles the entire real crt0, then extracts its preservation, relocation data
loop, BSS loop, publication and getter into a tiny user-mode executable. This
checks scalar/data/ABI behavior, not privileged cache maintenance, physical
memory ownership, DTB parsing, firmware boot, or PCI readiness. The deliberate
RWX segment is test-only trampoline scratch.
"""
from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
from pathlib import Path

TEMPLATE = r"""/* Reduced EL0 data/ABI fixture; NOT firmware/MMU/cache acceptance. */
.section .text,"ax",%progbits
.global _start
_start:
    ldr x0, =0xfedcba9876543210
#ifndef SABOTAGE_SAVE
@SAVE@
#endif
#ifdef SABOTAGE_EARLY_PUBLISH
@PUBLISH@
#endif
    /* Same early-logger clobber set as crt0: x0/x1/w2 and link register. */
    bl early_logger_clobber
#ifdef NO_RELOCATION
    b after_relocation
#endif
    adr x9, copied_image + 16
    adr x10, copied_image
    mov x11, #64
    adr x12, trampoline_scratch
    adr x13, .Lreloc_tramp
    adr x14, .Lreloc_tramp_end
    mov x15, x12
.Lfixture_tramp_copy:
    ldr x16, [x13], #8
    str x16, [x15], #8
    cmp x13, x14
    b.lo .Lfixture_tramp_copy
    adr x17, after_relocation
    br x12
.balign 8
@TRAMP@after_relocation:
    bl early_logger_clobber
    /* Fill then clear BSS to prove publishing before clear would lose it. */
    adr x0, _sbss
    adr x1, _ebss
    mov x2, #-1
.Lfill:
    str x2, [x0], #8
    cmp x0, x1
    b.lo .Lfill
    adr x0, _sbss
    adr x1, _ebss
@BSS@
#ifndef SABOTAGE_EARLY_PUBLISH
@PUBLISH@
#endif
    bl fixture_c_start
    /* C checks the 64-bit getter, image copy, and zeroed BSS. */
    mov x8, #93
    svc #0

early_logger_clobber:
    mov x0, #17
    mov x1, #18
    mov w2, #19
    ret

.global rt_arm64_boot_dtb_address
.type rt_arm64_boot_dtb_address,%function
@GETTER@.size rt_arm64_boot_dtb_address, .-rt_arm64_boot_dtb_address

.section .data,"aw",%progbits
.balign 8
.global copied_image
copied_image:
#ifdef NO_RELOCATION
    .quad 1,2,3,4,5,6,7,8,0,0
#else
    .quad 0,0,1,2,3,4,5,6,7,8
#endif
.section .bss,"aw",%nobits
.balign 8
.global _sbss, _ebss, bss_probe
_sbss:
@SLOT@: .skip 8
bss_probe: .skip 16
_ebss:
.section .fixture_scratch,"awx",%progbits
.balign 16
trampoline_scratch: .skip 256
"""
CHECKER = r"""typedef unsigned long long u64;
extern u64 rt_arm64_boot_dtb_address(void);
extern u64 copied_image[10], bss_probe[2];
int fixture_c_start(void) {
    if (rt_arm64_boot_dtb_address() != 0xfedcba9876543210ULL) return 11;
    for (unsigned i=0; i<8; ++i) if (copied_image[i] != i+1) return 12;
    if (bss_probe[0] || bss_probe[1]) return 13;
    return 0;
}
"""
LINKER = r"""ENTRY(_start)
PHDRS { code PT_LOAD FLAGS(5); data PT_LOAD FLAGS(6); scratch PT_LOAD FLAGS(7); }
SECTIONS {
 . = 0x400000;
 .text : { *(.text*) } :code
 . = ALIGN(0x10000);
 .data : { *(.data*) } :data
 .bss (NOLOAD) : { *(.bss*) } :data
 . = ALIGN(0x10000);
 .fixture_scratch : { *(.fixture_scratch) } :scratch
 /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
"""


def between(source: str, start: str, end: str) -> str:
    a = source.index(start)
    b = source.index(end, a + len(start))
    return source[a:b]


def fixture_source(source: str) -> str:
    entry = between(source, ".Lreloc_check:\n", "    adr     x9, _start")
    save = re.findall(r"^\s*mov\s+x20,\s*x0\s*$", entry, re.M)
    if len(save) != 1:
        raise ValueError("entry must preserve x0 in x20 before relocation/logging")
    entry_code = re.sub(r"/\*.*?\*/", "", entry, flags=re.S)
    entry_instructions = [line.strip() for line in entry_code.splitlines()[1:] if line.strip()]
    if len(entry_instructions) != 1 or not re.fullmatch(r"mov\s+x20,\s*x0", entry_instructions[0]):
        raise ValueError("x0 save must be the first executable instruction at relocation entry")
    header_code = re.sub(r"/\*.*?\*/", "", between(source, "_start:\n", "    .quad"), flags=re.S)
    header_instructions = [line.strip() for line in header_code.splitlines()[1:] if line.strip()]
    if len(header_instructions) != 2 or header_instructions[0] != "nop" or not re.fullmatch(r"b\s+\.Lreloc_check", header_instructions[1]):
        raise ValueError("Image header must reach the save without clobbering x0")
    before_publish = re.sub(r"/\*.*?\*/", "", between(source, ".Lreloc_check:\n", ".Lbss_done:\n"), flags=re.S)
    register_uses = [line.strip() for line in before_publish.splitlines() if re.search(r"\b[wx]20\b", line)]
    if len(register_uses) != 1 or not re.fullmatch(r"mov\s+x20,\s*x0", register_uses[0]):
        raise ValueError("early boot must reserve x20 until post-BSS publication")
    publish_region = between(source, ".Lbss_done:\n", "    adr     x0, .Lcrt0_bss")
    publication = "\n".join(line for line in publish_region.splitlines()
                            if line.strip().startswith(("adrp ", "add ", "str ")))
    slot_match = re.search(r"adrp\s+x9,\s*(\.L[A-Za-z0-9_]+)", publication)
    if not slot_match or not re.search(r"str\s+x20,\s*\[x9\]", publication):
        raise ValueError("post-BSS publication must store preserved x20")
    slot = slot_match.group(1)
    if not re.search(re.escape(slot) + r":\s*\n\s*\.skip\s+8", source):
        raise ValueError("raw slot must retain its eight-byte definition")
    trampoline = between(source, ".Lreloc_tramp:\n", ".Lreloc_tramp_end:\n")
    # IC IALLU is privileged. EL0 unit tests omit maintenance only; the full
    # real source is independently assembled and retained for inspection.
    trampoline = "\n".join(line for line in trampoline.splitlines()
                           if not line.strip().startswith(("dsb ", "ic ", "isb")))
    trampoline += "\n.Lreloc_tramp_end:\n"
    bss = between(source, ".Lbss_loop:\n", ".Lbss_done:\n") + ".Lbss_done:\n"
    getter = between(source, "rt_arm64_boot_dtb_address:\n",
                     "    .size rt_arm64_boot_dtb_address")
    fixture = TEMPLATE
    for marker, value in {"@SAVE@": save[0], "@PUBLISH@": publication,
                          "@TRAMP@": trampoline, "@BSS@": bss,
                          "@GETTER@": getter, "@SLOT@": slot}.items():
        fixture = fixture.replace(marker, value)
    return fixture


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="new evidence directory; existing paths are refused")
    parser.add_argument("--crt0", type=Path,
                        default=Path(__file__).resolve().parents[2] /
                        "examples/09_embedded/simple_os/arch/arm64/boot/crt0.S")
    args = parser.parse_args()
    tools = {}
    for name in ("clang", "ld.lld", "llvm-objdump", "llvm-readobj", "qemu-aarch64"):
        path = shutil.which(name)
        if path is None:
            raise RuntimeError("required fixture tool unavailable: " + name)
        tools[name] = path
    source = args.crt0.read_text()
    fixture = fixture_source(source)
    args.output.mkdir(parents=True, exist_ok=False)
    output = args.output.resolve()
    (output / "handoff.S").write_text(fixture)
    (output / "checker.c").write_text(CHECKER)
    (output / "checker-zero.c").write_text(CHECKER.replace("0xfedcba9876543210ULL", "0ULL"))
    (output / "handoff-zero.S").write_text(fixture.replace("ldr x0, =0xfedcba9876543210", "mov x0, #0"))
    (output / "fixture.ld").write_text(LINKER)
    records = []

    def run(command: list[str], name: str, expected: int = 0,
            timeout: int = 30) -> subprocess.CompletedProcess:
        result = subprocess.run(command, cwd=output, capture_output=True,
                                timeout=timeout, check=False)
        (output / (name + ".stdout")).write_bytes(result.stdout)
        (output / (name + ".stderr")).write_bytes(result.stderr)
        (output / (name + ".command")).write_text(repr(command) + "\n")
        records.append(f"    {name}, {result.returncode}, {expected}")
        if result.returncode != expected:
            raise RuntimeError(f"{name}: expected exit {expected}, got {result.returncode}; see {output}")
        return result

    try:
        run([tools["clang"], "--target=aarch64-none-elf", "-c", str(args.crt0.resolve()),
             "-o", "crt0.o"], "assemble-production")
        run([tools["llvm-objdump"], "-dr", "crt0.o"], "production-disassembly")
        run([tools["llvm-readobj"], "--file-headers", "--sections", "--relocations",
             "--symbols", "crt0.o"], "production-object")
        run([tools["clang"], "--target=aarch64-linux-gnu", "-ffreestanding",
             "-fno-stack-protector", "-fno-builtin", "-O1", "-c", "checker.c",
             "-o", "checker.o"], "compile-checker")
        run([tools["clang"], "--target=aarch64-linux-gnu", "-ffreestanding",
             "-fno-stack-protector", "-fno-builtin", "-O1", "-c", "checker-zero.c",
             "-o", "checker-zero.o"], "compile-checker-zero")
        for name, flags, expected in (
            ("relocated", [], 0),
            ("direct", ["-DNO_RELOCATION"], 0),
            ("missing-save", ["-DSABOTAGE_SAVE"], 11),
            ("early-publication", ["-DSABOTAGE_EARLY_PUBLISH"], 11),
            ("zero-raw", [], 0),
        ):
            assembly = "handoff-zero.S" if name == "zero-raw" else "handoff.S"
            checker = "checker-zero.o" if name == "zero-raw" else "checker.o"
            run([tools["clang"], "--target=aarch64-linux-gnu", *flags, "-c",
                 assembly, "-o", name + ".o"], "assemble-" + name)
            run([tools["ld.lld"], "-T", "fixture.ld", name + ".o", checker,
                 "-o", name + ".elf"], "link-" + name)
            run([tools["qemu-aarch64"], "./" + name + ".elf"],
                "execute-" + name, expected=expected, timeout=1)
    finally:
        digest = hashlib.sha256(source.encode()).hexdigest()
        (output / "evidence.sdn").write_text(
            "crt0_sha256: " + digest + "\n"
            "scope: reduced-el0-scalar-handoff-not-firmware-acceptance\n"
            "checks |name, actual_exit, expected_exit|\n" + "\n".join(records) + "\n")
    print("PASS ARM64 raw DTB handoff: direct/relocated/zero and two sabotage controls; "
          "reduced EL0 only; evidence=" + str(output))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        raise SystemExit("FAIL ARM64 raw DTB fixture: " + str(error)) from error
