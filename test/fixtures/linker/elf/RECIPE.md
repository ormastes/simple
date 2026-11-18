# ELF linker fixtures (lane A7 slice 1)

Tiny freestanding ET_REL objects for the internal static ELF linker specs
(`test/01_unit/compiler/backend/linker/elf_{exec_writer,archive_closure,static_link}_spec.spl`).
Each program writes `hi\n` and exits with status 42 (40 + `base` = 2).

Produced with `clang version 23.1.0 (ea7d852a70e8)` and `llvm-ar` from the same
install, run from this directory:

```
CF="-c -O1 -ffreestanding -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $CF start_a64.c  -o start_a64.o
clang --target=aarch64-linux-gnu $CF lib_a64.c    -o lib_a64.o
clang --target=aarch64-linux-gnu $CF mid_a64.c    -o mid_a64.o
clang --target=aarch64-linux-gnu $CF leaf_a64.c   -o leaf_a64.o
clang --target=aarch64-linux-gnu $CF unused_a64.c -o unused_a64.o
llvm-ar rcs libchain_a64.a mid_a64.o leaf_a64.o unused_a64.o
clang --target=x86_64-linux-gnu  $CF start_x64.c  -o start_x64.o
clang --target=x86_64-linux-gnu  $CF lib_x64.c    -o lib_x64.o
clang --target=x86_64-linux-gnu -c -ffreestanding -fno-pic -fno-stack-protector -fcommon common_x64.c -o common_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fno-pic -fno-stack-protector canonical_plt_x64.c -o canonical_plt_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fno-pic -fno-stack-protector tls_sections_x64.c -o tls_sections_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fno-pic -fno-stack-protector -ftls-model=local-exec tls_local_exec_x64.c -o tls_local_exec_x64.o
clang --target=x86_64-linux-gnu -c tls_tpoff64_x64.s -o tls_tpoff64_x64.o
clang --target=x86_64-linux-gnu -c symbol_size_x64.s -o symbol_size_x64.o
clang --target=x86_64-linux-gnu -c symbol_size_def_x64.s -o symbol_size_def_x64.o
clang --target=x86_64-linux-gnu -c pc64_x64.s -o pc64_x64.o
clang --target=x86_64-linux-gnu -c pc64_def_x64.s -o pc64_def_x64.o
clang --target=x86_64-linux-gnu -c pc_narrow_x64.s -o pc_narrow_x64.o
clang --target=x86_64-linux-gnu -c pc_narrow_def_x64.s -o pc_narrow_def_x64.o
clang --target=x86_64-linux-gnu -c abs_narrow_x64.s -o abs_narrow_x64.o
clang --target=x86_64-linux-gnu -c abs_narrow_def_x64.s -o abs_narrow_def_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -ftls-model=initial-exec tls_import_x64.c -o tls_import_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -ftls-model=global-dynamic tls_import_x64.c -o tls_global_dynamic_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -ftls-model=local-dynamic tls_sections_x64.c -o tls_local_dynamic_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -mtls-dialect=gnu2 tls_import_x64.c -o tls_desc_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -ftls-model=initial-exec tls_versioned_x64.c -o tls_versioned_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector tls_provider_x64.c -o tls_provider_x64.o
clang --target=aarch64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -ftls-model=initial-exec tls_import_a64.c -o tls_import_a64.o
clang --target=aarch64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector tls_provider_a64.c -o tls_provider_a64.o
ld.lld -shared --soname libtls_x64.so -o libtls_x64.so.1 tls_provider_x64.o
ld.lld -shared --soname libtls_versioned_x64.so.1 --version-script tls_version_x64.map -o libtls_versioned_x64.so.1 tls_provider_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fno-pic -fno-stack-protector -funwind-tables unwind_x64.c -o unwind_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -fmerge-all-constants merge_strings_a_x64.c -o merge_strings_a_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fPIC -fno-stack-protector -fmerge-all-constants merge_strings_b_x64.c -o merge_strings_b_x64.o
clang --target=x86_64-linux-gnu -c merge_const_a_x64.s -o merge_const_a_x64.o
clang --target=x86_64-linux-gnu -c merge_const_b_x64.s -o merge_const_b_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fno-pic -fno-stack-protector -fno-unwind-tables -fno-asynchronous-unwind-tables -ffunction-sections -fdata-sections gc_sections_x64.c -o gc_sections_x64.o
clang --target=x86_64-linux-gnu -c -O1 -ffreestanding -fno-pic -fno-stack-protector -funwind-tables -ffunction-sections -fdata-sections gc_sections_x64.c -o gc_unwind_x64.o
```

Relocations exercised (`llvm-readelf -r`):

| object | relocations |
|---|---|
| start_a64.o | ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC (msg), CALL26 (add_val) |
| lib_a64.o | ADR_PREL_PG_HI21 + LDST64_ABS_LO12_NC (base, scratch) |
| mid_a64.o | JUMP26 (tail call to leaf_fn) |
| start_x64.o | R_X86_64_32 (msg), PLT32 (add_val) |
| lib_x64.o | PC32 (base, scratch) |
| common_x64.o | R_X86_64_32S (`shared_block`); `SHN_COMMON`, size 48, alignment 32 |
| canonical_plt_x64.o | R_X86_64_64 (`add_val`) in `.data`, resolved to the executable's canonical PLT entry |
| tls_sections_x64.o | `.tdata` + `.tbss` with `SHF_TLS`; two R_X86_64_TPOFF32 references keep both templates live for PT_TLS layout |
| tls_local_exec_x64.o | R_X86_64_TPOFF32 (`local_tls`), resolved relative to the end of the static TLS block |
| tls_tpoff64_x64.o | static R_X86_64_TPOFF64 data word resolved as the signed offset from the TLS block end |
| symbol_size_{x64,def_x64}.o | cross-object R_X86_64_SIZE32/SIZE64 relocations resolved from the defining symbol extent |
| pc64_{x64,def_x64}.o | cross-object R_X86_64_PC64 resolved as the full-width `S + A - P` delta; ld.lld 23.1 oracle bytes are `f8 df ff ff ff ff ff ff` |
| pc_narrow_{x64,def_x64}.o | cross-object R_X86_64_PC16/PC8 with checked signed widths; ld.lld 23.1 `.data` oracle is `03 00 01 6b` |
| abs_narrow_{x64,def_x64}.o | cross-object R_X86_64_16/8 against absolute symbols with checked unsigned widths; ld.lld 23.1 `.data` oracle is `34 12 7f` |
| tls_import_x64.o | R_X86_64_GOTTPOFF (`imported_tls`), bound through a GOT slot carrying R_X86_64_TPOFF64 |
| tls_import_a64.o | ADR_GOTTPREL_PAGE21 + LD64_GOTTPREL_LO12_NC (`imported_tls`), bound through a variant-I TPREL GOT slot |
| tls_global_dynamic_x64.o | canonical R_X86_64_TLSGD + `__tls_get_addr` sequence, relaxed to initial-exec/TPOFF64 |
| tls_local_dynamic_x64.o | canonical R_X86_64_TLSLD + `__tls_get_addr` with DTPOFF32 uses, relaxed to local-exec/TPOFF32 |
| tls_desc_x64.o | canonical GOTPC32_TLSDESC + TLSDESC_CALL pair, relaxed to GOTTPOFF/TPOFF64 with a two-byte NOP |
| tls_versioned_x64.o | explicit `imported_tls@TLS_1.0` initial-exec import with `.gnu.version`/`.gnu.version_r` output |
| unwind_x64.o | two zR/pcrel-sdata4 FDEs indexed by `.eh_frame_hdr` |
| gc_sections_x64.o | entry-rooted relocation graph retaining live function/data/BSS while dropping dead function/data sections |
| gc_unwind_x64.o | four input FDEs reduced to the two live-function FDEs, with compacted CIE pointers and relocation offsets |
| merge_strings_{a,b}_x64.o | duplicate `.rodata.str1.1` fragments coalesce and both local-symbol relocations resolve to the pooled string |
| merge_const_{a,b}_x64.o | duplicate aligned `.rodata.cst8` entities coalesce and both PC-relative relocations resolve to the pooled constant |

The specs depend on the exact byte offsets noted in them (e.g. the CALL26 at
`_start+0x24`, x86_64 `call` rel32 at `.text+0x1d`); regenerate the specs'
constants if these objects are rebuilt with a different compiler.

## Slice 2 fixtures (GOT, static PIE, dynamic libc)

Same compiler, run from this directory:

```
PIC="-c -O1 -ffreestanding -fPIC -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
PIE="-c -O1 -ffreestanding -fPIE -fvisibility=hidden -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $PIC start_a64.c -o pic_start_a64.o
clang --target=aarch64-linux-gnu $PIC lib_a64.c   -o pic_lib_a64.o
clang --target=x86_64-linux-gnu  $PIC start_x64.c -o pic_start_x64.o
clang --target=x86_64-linux-gnu  $PIC lib_x64.c   -o pic_lib_x64.o
clang --target=aarch64-linux-gnu $PIE -fdirect-access-external-data start_a64.c -o pie_start_a64.o
clang --target=aarch64-linux-gnu $PIE lib_a64.c   -o pie_lib_a64.o
clang --target=x86_64-linux-gnu  $PIE start_x64.c -o pie_start_x64.o
clang --target=x86_64-linux-gnu  $PIE lib_x64.c   -o pie_lib_x64.o
clang --target=x86_64-linux-gnu -c gotpc32_x64.s -o gotpc32_x64.o
clang --target=x86_64-linux-gnu -c got32_x64.s -o got32_x64.o
clang --target=x86_64-linux-gnu -c got64_x64.s -o got64_x64.o
clang --target=x86_64-linux-gnu -c gotpcrel64_x64.s -o gotpcrel64_x64.o
clang --target=x86_64-linux-gnu -c gotpc64_x64.s -o gotpc64_x64.o
clang --target=x86_64-linux-gnu -c code4_gotpcrelx_x64.s -o code4_gotpcrelx_x64.o
clang --target=x86_64-linux-gnu -c code_gottpoff_x64.s -o code_gottpoff_x64.o
clang --target=x86_64-linux-gnu -c gotoff64_x64.s -o gotoff64_x64.o
clang --target=x86_64-linux-gnu -c pltoff64_x64.s -o pltoff64_x64.o
clang --target=aarch64-linux-gnu -c -O1 -fPIE -fno-asynchronous-unwind-tables -fno-unwind-tables hello_libc.c -o hello_libc_a64.o
```

| object | relocations |
|---|---|
| pic_start_a64.o | ADR_GOT_PAGE (+4) + LD64_GOT_LO12_NC (+0x10) (msg), CALL26 (add_val) |
| pic_lib_a64.o | ADR_GOT_PAGE + LD64_GOT_LO12_NC (base, scratch) — pairs not adjacent, so ld.lld keeps the GOT |
| pic_start_x64.o | REX_GOTPCRELX (msg, `mov` at .text+1, opcode byte +2), PLT32 (add_val) |
| pic_lib_x64.o | REX_GOTPCRELX (scratch, base) |
| pie_start_a64.o | ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC (msg), CALL26 (add_val) |
| pie_lib_a64.o | ADR_PREL_PG_HI21 + LDST64_ABS_LO12_NC (base, scratch) |
| pie_start_x64.o | REX_GOTPCRELX (msg, relaxed to `lea`), PLT32 (add_val) |
| pie_lib_x64.o | PC32 (scratch, base) |
| hello_libc_a64.o | ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC (.rodata.str1.1), CALL26 (puts, exit); `main` is in `.text.unlikely.` |
| gotpc32_x64.o | explicit R_X86_64_GOTPC32 reference to the linker-synthesized `_GLOBAL_OFFSET_TABLE_` |
| got32_x64.o | explicit R_X86_64_GOT32 offset from `_GLOBAL_OFFSET_TABLE_` to a local symbol's GOT slot |
| got64_x64.o | explicit full-width R_X86_64_GOT64 offset from `_GLOBAL_OFFSET_TABLE_` to a local symbol's GOT slot |
| gotpcrel64_x64.o | explicit `.reloc` R_X86_64_GOTPCREL64 full-width displacement from the patch address to a local symbol's GOT slot |
| gotpc64_x64.o | explicit `.reloc` R_X86_64_GOTPC64 full-width displacement to the linker-synthesized `_GLOBAL_OFFSET_TABLE_` |
| code4_gotpcrelx_x64.o | explicit `.reloc` R_X86_64_CODE_4_GOTPCRELX signed 32-bit displacement to a local symbol's GOT slot; kept unrelaxed and checked against Mold 2.42 |
| code_gottpoff_x64.o | explicit `.reloc` R_X86_64_CODE_4_GOTTPOFF and R_X86_64_CODE_6_GOTTPOFF initial-exec displacements sharing a local TLS TPOFF GOT slot; checked against Mold 2.42 |
| gotoff64_x64.o | explicit `.reloc` R_X86_64_GOTOFF64 full-width displacement from `_GLOBAL_OFFSET_TABLE_` to a local data symbol; Mold 2.42 supplies the byte oracle |
| pltoff64_x64.o | explicit `.reloc` R_X86_64_PLTOFF64 full-width displacement from `.got.plt` to a local function; Mold 2.42 supplies the byte oracle |

`hello_libc_a64.o` is linked by `elf_dynamic_link_spec` and `link_engine_external_spec`
together with the HOST glibc startup objects and `libc.so.6` from
`/usr/lib/aarch64-linux-gnu` (not vendored here), so those specs need an aarch64
Linux host with glibc. It prints `hi from libc` and exits 42.

## Lane B2 fixtures (.gnu.hash oracle, x86_64 dynamic)

Same compiler + `ld.lld` from the same install, run from this directory. The
shared objects carry a `.1` suffix because the repo `.gitignore` drops `*.so`:

```
PIC="-c -O1 -ffreestanding -fPIC -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $PIC gnu_hash_syms.c -o gnu_hash_syms_a64.o
ld.lld -shared --soname libgnuhash.so --hash-style=both -o libgnuhash_a64.so.1 gnu_hash_syms_a64.o
ld.lld -shared --soname libadd_x64.so --hash-style=both -o libadd_x64.so.1 pic_lib_x64.o
```

| file | role |
|---|---|
| libgnuhash_a64.so.1 | `.gnu.hash` oracle: 11 exports -> 2 buckets, 4 bloom words, symoffset 1 (`llvm-readelf --gnu-hash-table`); `elf_gnu_hash_spec` rebuilds it byte for byte from its `.dynsym` names |
| libadd_x64.so.1 | x86_64 DSO exporting add_val / msg / base / scratch (soname `libadd_x64.so`); `elf_x64_dynamic_spec` links `pic_start_x64.o` against it: add_val via PLT32 -> PLT1 + R_X86_64_JUMP_SLOT, msg via REX_GOTPCRELX (kept as `mov`, import) -> .got + R_X86_64_GLOB_DAT |

The x86_64 dynamic outputs are compared with
`ld.lld --dynamic-linker /lib64/ld-linux-x86-64.so.2 [-pie] pic_start_x64.o libadd_x64.so.1`
(`llvm-readelf -l -S -d -r`, `llvm-objdump -d --section=.plt`). They are never
executed: this aarch64 host has no x86_64 glibc or ld-linux-x86-64.so.2.

## ELF32 fixtures (i386 + armv7, internal linker ELF32 lane)

`elf32_hello.c` writes `hello internal linker\n` three times and exits 42 via
`helper(40)` in `elf32_helper.c`. Produced with `Ubuntu clang version 18.1.3`:

```
CF="-c -O1 -ffreestanding -fno-stack-protector -fno-asynchronous-unwind-tables -fno-unwind-tables"
clang --target=i686-linux-gnu $CF -fno-pic elf32_hello.c  -o elf32_hello_i386.o
clang --target=i686-linux-gnu $CF -fno-pic elf32_helper.c -o elf32_helper_i386.o
clang --target=i686-linux-gnu $CF -fPIC   elf32_hello.c  -o elf32_hello_i386_pic.o   # GOTPC/GOTOFF/PLT32
clang --target=i686-linux-gnu $CF -fPIC   elf32_helper.c -o elf32_helper_i386_pic.o  # GOTPC/GOT32X
clang --target=armv7-linux-gnueabihf $CF -fno-pic elf32_hello.c  -o elf32_hello_arm.o
clang --target=armv7-linux-gnueabihf $CF -fno-pic elf32_helper.c -o elf32_helper_arm.o
```

clang --target=i686-linux-gnu -c elf32_got32_nobase_i386.s -o elf32_got32_nobase_i386.o  # GOT32 without base register

## elf32_hello_arm_soft.o / elf32_helper_arm_soft.o

Same sources (`elf32_hello.c` / `elf32_helper.c`), built soft-float
(no Tag_ABI_VFP_args) for the EF_ARM_ABI_FLOAT_SOFT e_flags test:

    clang --target=armv7-linux-gnueabihf -mfloat-abi=soft -ffreestanding -fno-pic -O1 -c elf32_hello.c -o elf32_hello_arm_soft.o
    clang --target=armv7-linux-gnueabihf -mfloat-abi=soft -ffreestanding -fno-pic -O1 -c elf32_helper.c -o elf32_helper_arm_soft.o

## Boot-linker SHF_MERGE fixtures (work/boot-link-shf-merge-20261118)

`elf_boot_link_merge_spec.spl` pools SHF_MERGE|SHF_STRINGS through the boot
linker and byte-compares with ld.lld. From this directory, with the llvm-mingw
23.1.0 clang/ld.lld:

```
CF="-c -O1 -ffreestanding -fno-pic -fno-stack-protector -fno-asynchronous-unwind-tables -fno-unwind-tables -fmerge-all-constants -nostdlib"
clang --target=aarch64-linux-gnu $CF boot_merge_a_a64.c -o boot_merge_a_a64.o
clang --target=aarch64-linux-gnu $CF boot_merge_b_a64.c -o boot_merge_b_a64.o
clang --target=x86_64-linux-gnu $CF merge_strings_a_x64.c -o boot_merge_a_x64.o
clang --target=x86_64-linux-gnu $CF merge_strings_b_x64.c -o boot_merge_b_x64.o
ld.lld -m aarch64linux --no-relax -T boot_merge_a64.ld boot_merge_a_a64.o boot_merge_b_a64.o -o ref_a64.elf
ld.lld -m elf_x86_64 -T boot_merge_x64.ld boot_merge_a_x64.o boot_merge_b_x64.o -o ref_x64.elf
for a in a64 x64; do for s in text rodata; do
  llvm-objcopy -O binary --only-section=.$s ref_$a.elf boot_merge_$a.lld.$s.bin; done; done
```

Reference symbol values (llvm-readelf -s): a64 first_message 0x40000000,
_start 0x4000000c, other_message 0x4000004c, tail_message 0x40000058,
string_sink 0x40000098; x64 long_message 0x400000, _start 0x400010,
short_message 0x400030, string_sink 0x400048.
## tls_ie_arm.o / tls_ie_def_arm.o

armv7 initial-exec TLS through an R_ARM_TLS_IE32 GOT slot (ld.lld slot = 0xc):

    clang --target=armv7-linux-gnueabihf -mtp=cp15 -ffreestanding -fPIC -O1 -c tls_ie_arm.c -o tls_ie_arm.o
    clang --target=armv7-linux-gnueabihf -ffreestanding -fPIC -O1 -c tls_ie_def_arm.c -o tls_ie_def_arm.o

## ifunc_sym_x64.o

Static IFUNC called directly and address-taken (`.quad add_val`); ld.lld makes
`add_val` STT_FUNC at the `.iplt` entry:

    clang --target=x86_64-linux-gnu -c ifunc_sym_x64.s -o ifunc_sym_x64.o

## thm_call_notype_arm.o / thm_call_notype_def_arm.o

Thumb `bl` to a NOTYPE Thumb label; ld.lld keeps BL (no interworking for non-STT_FUNC):

    clang --target=armv7-linux-gnueabihf -c thm_call_notype_arm.s -o thm_call_notype_arm.o
    clang --target=armv7-linux-gnueabihf -c thm_call_notype_def_arm.s -o thm_call_notype_def_arm.o

## gottpoff_addend_x64.o

GOTTPOFF with addend -4 on a raw field (no relaxation); slot = tprel(S) = -8:

    clang --target=x86_64-linux-gnu -c gottpoff_addend_x64.s -o gottpoff_addend_x64.o

## ELF32 dynamic fixtures (i386, lane c)

`Ubuntu clang version 18.1.3`, run from this directory:

```
PIC="-c -O1 -ffreestanding -fPIC -fno-stack-protector -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=i686-linux-gnu $PIC dyn_start_i386.c -o dyn_start_i386.o
clang --target=i686-linux-gnu $PIC dyn_lib_i386.c -o dyn_lib_i386.o
ld.lld -shared --soname libadd_i386.so --hash-style=both -o libadd_i386.so.1 dyn_lib_i386.o
```

| file | role |
|---|---|
| dyn_start_i386.o | GOTPC (_GLOBAL_OFFSET_TABLE_), GOT32X (msg, import -> .got + R_386_GLOB_DAT), PLT32 (add_val -> PLT1 + R_386_JUMP_SLOT); writes msg and exits 42 via int $0x80 |
| libadd_i386.so.1 | ELF32 DSO exporting add_val / msg / base / scratch (soname `libadd_i386.so`) |

`elf32_dynamic_spec` checks the output against
`ld.lld --dynamic-linker /lib/ld-linux.so.2 [-pie] dyn_start_i386.o libadd_i386.so.1`;
both run under `qemu-i386-static -L /usr/i686-linux-gnu` and print `hi`, exit 42.
