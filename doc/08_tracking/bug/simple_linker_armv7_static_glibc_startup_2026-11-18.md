# Simple linker: armv7 static glibc crashed at startup (5 root causes)

- **Status:** verification-pending
- **Found:** 2026-11-18, after static IFUNC support (#10254) let armv7 static glibc link
- **Area:** `src/compiler/70.backend/linker/` (elf_static_link, reloc_engine, elf_parser)

## Symptom

`hello_libc_static_slk` (crt1/crti/hello_libc.o/crtn + libc.a, armv7 hard-float)
linked, then SIGSEGVed under `qemu-arm-static` in `_dl_debug_vdprintf`. The same
inputs linked by ld.lld 18 ran and printed `hello libc 1 tls=8`.

## Root causes (found one after another by diffing against the ld.lld output and tracing with `qemu -d exec`)

1. **PT_TLS block split.** Unnamed RW PROGBITS sections defaulted to the same
   sort rank as `.tdata`. `.igot.plt` landed between `.tdata` and `.tbss`, so
   PT_TLS memsz was 0x38 instead of 0x30. Fix: `.tdata` (or any SHF_TLS
   PROGBITS) ranks 38 and every other RW section ranks 37.
   Spec: `elf_tls_order_spec.spl`.
2. **R_ARM_THM_CALL never interworked to ARM code.** A Thumb `bl` to an ARM
   function (glibc `memset`) stayed `bl`, so `memset` ran in Thumb state. Fix:
   when the target is even, emit BLX, offset from Align(P,4), with bit 12 of
   the low half cleared. An existing BLX to a Thumb target becomes BL. The BL
   value is masked to 25 bits, so a backward branch never sets the bit-26 BLX
   marker. Spec: `reloc_engine_spec.spl`.
3. **TLS IE GOT slot held tprel(S + A).** On ARM (REL), A is the literal-pool
   PC bias, which belongs to the `GOT(S) + A - P` access and not to the slot.
   Fix: the slot holds tprel(S), as ld.lld writes it.
   Spec: `elf_got_static_spec.spl` with fixtures `tls_ie_arm.o` and `tls_ie_def_arm.o`.
4. **MOVW/MOVT REL implicit addend.** MOVT read imm16 << 16. AAELF and ld.lld
   use SignExtend(imm16) for both halves. The glibc `setjmp.o` `movt #0xfff4`
   (A = -12) put the GOT base 0xc0000 too low. Spec: `elf_parser_spec.spl`.
   The two old expectations of 0x12340000 were wrong and are corrected to 0x1234.
5. **ARM `_GLOBAL_OFFSET_TABLE_` marked `.got.plt`.** GOT_BREL and BASE_PREL
   are computed from `.got`. ld.lld puts the symbol on `.got` for ARM
   (`gotBaseSymInGotPlt` is false there). `__sigsetjmp` loaded `_dl_hwcap` from
   `.bss`. Fix: `elf_got_base_sec(target)`, and `.got` is now always emitted on
   ARM when the GOT base is referenced. Spec: `elf_got_static_spec.spl`.

## Evidence

- Each new spec failed against the unfixed linker and passes after the fix:
  reloc_engine 130/130, elf_got_static 9/9, elf_tls_order 1/1.
  elf_parser is 29/30; the remaining failure, "width-correct ARM absolute and
  TARGET1", also fails on the base. Regression checks: elf_static_link 7/7,
  elf_static_pie 5/5, elf_boot_link 48/48, iplt 6/6, veneer 5/5, tls_relax 11/11.
- `qemu-arm-static hello_libc_static_slk` prints `hello libc 1 tls=8`, the same
  as the ld.lld build.
- Link time: about 10 s (Simple linker, seed interpreter) against about 0.1 s for ld.lld.

## Remaining

- `.ARM.exidx` is not emitted. ld.lld emits it with PT_ARM_EXIDX. The hello
  program runs without it, but C++ or unwinding through glibc would need it.
- The i686 static glibc link is still blocked on `__letf2` / `__unordtf2`
  (owner decision pending).
