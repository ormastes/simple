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
```

Relocations exercised (`llvm-readelf -r`):

| object | relocations |
|---|---|
| start_a64.o | ADR_PREL_PG_HI21 + ADD_ABS_LO12_NC (msg), CALL26 (add_val) |
| lib_a64.o | ADR_PREL_PG_HI21 + LDST64_ABS_LO12_NC (base, scratch) |
| mid_a64.o | JUMP26 (tail call to leaf_fn) |
| start_x64.o | R_X86_64_32 (msg), PLT32 (add_val) |
| lib_x64.o | PC32 (base, scratch) |

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
(`llvm-readelf -l -S -d -r`, `llvm-objdump -d --section=.plt`). The execution
proof for x86_64 dynamic linking is the glibc hello below (lane C2).

## Lane C1 fixture (RELRO)

`relro_a64.o` gives a dynamic PIE one input section for every PT_GNU_RELRO
member ld.lld places: `.init_array` (constructor), `.fini_array` (destructor),
`.data.rel.ro` (a `const` table of code pointers), plus `.got`/`.dynamic` from
the link itself and a non-RELRO `.data`/`.got.plt`/`.bss`. It prints
`relro ok` and exits 42. Same compiler as above, run from this directory:

```
clang --target=aarch64-linux-gnu -c -O1 -fPIE -fno-asynchronous-unwind-tables \
    -fno-unwind-tables relro_a64.c -o relro_a64.o
```

RELRO oracle for `elf_relro_spec` (needs the host glibc startup objects, like
`hello_libc_a64.o`):

```
ld.lld-23 -pie -dynamic-linker /lib/ld-linux-aarch64.so.1 \
    /usr/lib/aarch64-linux-gnu/Scrt1.o /usr/lib/aarch64-linux-gnu/crti.o \
    relro_a64.o /usr/lib/aarch64-linux-gnu/crtn.o \
    /usr/lib/aarch64-linux-gnu/libc.so.6 -o rpie_lld
```

## Lane C1 fixture (--gc-sections)

`gc_a64.o` is built with `-ffunction-sections -fdata-sections`, so every
function and datum is its own input section: a live chain from `_start`
(`gc_add` -> `gc_leaf`, `gc_msg`, `gc_base`, `gc_scratch`), an unreferenced
dead chain (`gc_dead` -> `gc_dead_leaf`, `gc_dead_msg`, `gc_dead_base`,
`gc_dead_scratch`), an `SHF_GNU_RETAIN` function (`gc_retained`), a `.init`
function (`gc_in_init`) and a function reachable only through `.init_array`
(`gc_ctor`). It writes `gc\n` and exits 42.

```
clang --target=aarch64-linux-gnu -c -O1 -ffreestanding -fno-pic \
    -ffunction-sections -fdata-sections -fno-asynchronous-unwind-tables \
    -fno-unwind-tables -nostdlib gc_a64.c -o gc_a64.o
```

GC oracle for `elf_gc_sections_spec`:

```
ld.lld-23 -static -e _start --gc-sections --print-gc-sections gc_a64.o -o gcy
ld.lld-23 -static -e _start gc_a64.o -o gcn
```

## Lane C1 fixtures (SHF_MERGE string merge)

`merge_a_a64.o` and `merge_b_a64.o` share the literals `hi\n` and `dup\n` and
each add one of their own, so a `-O1` link must drop two duplicates. `_start`
compares `a_dup()` with `b_dup()` and adds 2 only when they merged to one
address: exit 42 means merged, exit 40 means not. Same compiler as above:

```
CF="-c -O2 -ffreestanding -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $CF merge_a_a64.c -o merge_a_a64.o
clang --target=aarch64-linux-gnu $CF merge_b_a64.c -o merge_b_a64.o
```

(`-fmerge-constants` is accepted by gcc but warned-and-ignored by this clang;
clang emits `.rodata.str1.1` as `SHF_MERGE|SHF_STRINGS` regardless, which is
what the merge path consumes.)

Merge oracle for `elf_merge_strings_spec`:

```
ld.lld-23 -static -e _start -O1 merge_a_a64.o merge_b_a64.o -o mrg1   # .rodata 0x19, exit 42
ld.lld-23 -static -e _start -O0 merge_a_a64.o merge_b_a64.o -o mrg0   # .rodata 0x22, exit 40
```

### Wide-literal, end-of-section and demotion fixtures (lane C1 review)

`merge_wide_a64.o` + `merge_wideb_a64.o` share one `L"wide"` literal in
`.rodata.str4.4` (`SHF_MERGE|SHF_STRINGS`, `sh_entsize 4`); ld.lld MERGES
multi-byte strings (`splitStrings` -> `findNull` scans entsize-sized NUL
units), so `-O1` gives one copy and exit 42, `-O0` two copies and exit 40.
`merge_strend_a64.o` defines a global at the very END of a merged section
(`st_value == sh_size`), which ld.lld accepts: for a named Defined symbol
`splitSections` (SyntheticSections.cpp) anchors any `v >= size` on the last
piece, and the `offset > size` error in `getSymVA` applies only to SECTION
symbols plus addend.
`merge_relin_a64.o` has `.rodata.cst8` holding `.quad target`, i.e. a
relocation INTO a merge section, which ld.lld demotes to a regular input
section. All three exit 42.

```
CF="-c -O2 -ffreestanding -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
for f in merge_wide_a64 merge_wideb_a64 merge_strend_a64 merge_relin_a64; do
  clang --target=aarch64-linux-gnu $CF $f.c -o $f.o
done
ld.lld-23 -static -e _start -O1 merge_wide_a64.o merge_wideb_a64.o   # .rodata 0x14 es 4, exit 42
ld.lld-23 -static -e _start -O0 merge_wide_a64.o merge_wideb_a64.o   # .rodata 0x28 es 4, exit 40
ld.lld-23 -static -e _start -O1 merge_strend_a64.o                   # links, exit 42
ld.lld-23 -static -e _start -O1 merge_relin_a64.o                    # .rodata 0x08 AM es 8
ld.lld-23 -static -e _start -O1 merge_relin_a64.o merge_b_a64.o      # .rodata 0x19 es 0
```

### Named-symbol + non-zero addend fixture (C1+C2 merge)

`merge_naddend_a64.o` pins ld.lld's `getSymVA` rule natively on aarch64: the
relocation addend is folded INTO the merge piece lookup only for an
`STT_SECTION` symbol; a NAMED symbol is anchored at `st_value` and the addend
applied afterwards. `.rodata.str1.1` holds `"dup\0"` twice, so merging puts
`s1` (st_value 0) and `s2` (st_value 4, `NOTYPE LOCAL`) on one address P, and
the reference is `s2 - 4` — correct gives `P - 4`, folding gives `P`. `_start`
exits 42 when `s1 - (s2 - 4)` is 4 and 40 when it is 0. This is the aarch64
twin of x86_64's `R_X86_64_PC32 .L.str - 4` in `hello_libc_x64.o`, which is
what first exposed the defect but needs the glibc sysroot and qemu to reach;
the twin is why mutation row `merge_addend_folded_for_named_symbol` can point
at a spec that runs on any aarch64 host.

```
CF="-c -O2 -ffreestanding -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -nostdlib"
clang --target=aarch64-linux-gnu $CF merge_naddend_a64.c -o merge_naddend_a64.o
ld.lld-23 -static -e _start -O1 merge_naddend_a64.o                  # .rodata 0x4, exit 42
ld.lld-23 -static -e _start -O0 merge_naddend_a64.o                  # exit 40
```

## Lane C2 fixture (x86_64 dynamic glibc execution proof)

`hello_libc_x64.o` is the x86_64 build of `hello_libc.c` (R_X86_64_PC32
`.L.str`, PLT32 `puts`, PLT32 `exit`; `main` in `.text.unlikely.`). It needs
x86_64 glibc headers, taken from the sysroot described next:

```
clang --target=x86_64-linux-gnu --sysroot=$HOME/.cache/x64-sysroot/root \
  -c -O1 -fPIE -fno-asynchronous-unwind-tables -fno-unwind-tables hello_libc.c -o hello_libc_x64.o
```

`elf_x64_dynamic_exec_spec` links it with the sysroot's `crt1.o`/`Scrt1.o`,
`crti.o`, `crtn.o` and `libc.so.6` into a dynamic ET_EXEC and PIE and runs both
with `qemu-x86_64 -L <sysroot>` (or natively on an x86_64 host): each prints
`hi from libc` and exits 42. The sysroot is NOT vendored. It is built without
root from Ubuntu noble amd64 packages, using a private apt state directory
(the host needs no amd64 foreign architecture):

```
S=$HOME/.cache/x64-sysroot
mkdir -p $S/apt/lists/partial $S/apt/cache/archives/partial $S/debs && touch $S/apt/status
printf 'deb [arch=amd64] http://archive.ubuntu.com/ubuntu noble main\ndeb [arch=amd64] http://archive.ubuntu.com/ubuntu noble-updates main\n' > $S/apt/sources.list
A="-o Dir::Etc::SourceList=$S/apt/sources.list -o Dir::Etc::SourceParts=/dev/null -o Dir::State::Lists=$S/apt/lists -o Dir::Cache=$S/apt/cache -o Dir::State::Status=$S/apt/status -o APT::Architecture=amd64 -o APT::Architectures=amd64"
apt-get $A update
cd $S/debs && apt-get $A download libc6 libc6-dev libgcc-s1 linux-libc-dev libcrypt-dev
for d in *.deb; do dpkg-deb -x $d $S/root; done
cd $S/root && ln -sfn usr/lib lib && ln -sfn usr/lib64 lib64
```

Packages used for the recorded run (sha256):

| package | sha256 |
|---|---|
| libc6_2.39-0ubuntu8.9_amd64.deb | ff5557d99b51f761c4b7c92368b9cc45565eda17df9bf9eb4b134d09825008be |
| libc6-dev_2.39-0ubuntu8.9_amd64.deb | e13d5fcc1b2a86f75bca8e0026a8e39f24fe97ca86e92be79991f8697eb1306f |
| libcrypt-dev_1%3a4.4.36-4build1_amd64.deb | 2edff420ef80b4a3f3751e65c33423ef30e563122a58b759e4854ea8d84ba1b1 |
| libgcc-s1_14.2.0-4ubuntu2~24.04.1_amd64.deb | aa7fadbe33b78bcf99885318040601c550c208929565b179891d9a3cc2aa68cd |
| linux-libc-dev_6.8.0-139.139_amd64.deb | f8292b3414cac372ec28ba484a45e3f18b3ac5fc7872ca82661835286f1c5865 |

Set `SIMPLE_X64_SYSROOT` to use another sysroot, and `SIMPLE_QEMU_X86_64` for a
specific qemu. When either is missing the spec prints `SKIP: x64-sysroot-missing`
or `SKIP: qemu-x86_64-missing` and asserts that reason.

### Lane C2 reject/versioning fixtures

Same compiler and sysroot:

```
CF="-c -O1 -fPIE -fno-asynchronous-unwind-tables -fno-unwind-tables"
clang --target=x86_64-linux-gnu --sysroot=$HOME/.cache/x64-sysroot/root $CF realpath_ver.c -o realpath_ver_x64.o
clang --target=x86_64-linux-gnu --sysroot=$HOME/.cache/x64-sysroot/root -c -O0 -fPIE \
  -fno-asynchronous-unwind-tables -fno-unwind-tables ifunc.c -o ifunc_x64.o
clang --target=x86_64-linux-gnu --sysroot=$HOME/.cache/x64-sysroot/root $CF -ftls-model=initial-exec \
  tls_ie.c -o tls_ie_x64.o
```

| object | role |
|---|---|
| realpath_ver_x64.o | `realpath("/", NULL)`: glibc has `realpath@GLIBC_2.2.5` (compat, returns NULL) and `realpath@@GLIBC_2.3`. Without `.gnu.version`/`.gnu.version_r` the reference binds to the library's version index 2 — GLIBC_2.2.5 on x86_64 — and the program exits 7 with no error. `elf_x64_dynamic_exec_spec` requires `realpath=/` and exit 42 |
| ifunc_x64.o | a locally defined `STT_GNU_IFUNC` (`f`). ld.lld emits R_X86_64_IRELATIVE and the program exits 42; without one the address is the resolver's (measured rc=192), so `elf_link` rejects it by name |
| tls_ie_x64.o | one R_X86_64_GOTTPOFF against an extern `__thread`. Kept as the shape that used to be misdiagnosed as "needs a copy relocation ... recompile with -fPIC"; the TLS classification is asserted directly in `elf_link_unsupported_spec` |
| symver_x64.o | `__asm__(".symver realpath, realpath@GLIBC_2.2.5")`: an explicit, non-default symbol version. Refused by name — this linker binds every reference to its library's default version. Built with the same flags as `realpath_ver_x64.o` |
