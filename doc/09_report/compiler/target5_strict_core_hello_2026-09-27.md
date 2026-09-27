# Target 5 strict core-C hello diagnostic (2026-09-27)

The historical admitted pure-Simple Stage2 compiler (SHA-256
`319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`)
built `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` through
Cranelift with `--runtime-bundle core-c-bootstrap --entry-closure --mode
one-binary --threads 1` and `SIMPLE_NO_STUB_FALLBACK=1`. The build exited 0
in 3.44 seconds, peaked at 192,088 KiB, and the output printed `hello`.

| Artifact | Size | SHA-256 |
| --- | ---: | --- |
| Unstripped ELF | 35,344 bytes | `19043058dca9419419189d21731e10311c6ee5450d5beb7d274b428b2ec74993` |
| `strip -s` ELF | 19,912 bytes | `c7111a26d3dfb7ec4e6fd0abf56d3f3c1b8c50472846d2eaf4a3599ec113f472` |

The previous non-strict diagnostic of the same Simple fixture recorded a
20,840-byte stripped ELF with 28 generated unresolved-symbol stubs. This
strict artifact is 928 bytes smaller; `nm` shows no weak `accept4`, `globfree`,
or `pthread_getspecific` stub definitions. `globfree` remains a dynamic libc
reference. The two builds were not taken from an immutable paired source
snapshot, so the size delta is diagnostic, not a controlled attribution.

The strict stripped artifact still exceeds the Linux 15 KiB release-small
hard budget by 4,552 bytes. This compiler's admission receipt names a deleted
source snapshot; there is no current-source Stage4 product, matched C size
cohort, startup p95, max RSS cohort, or optional-provider trace admission.
The BS7 target remains open. The exact build log and artifacts are under
`build/mini_builds/target5_strict_core_hello_20260927/`.

## Size attribution lead

`size -A` reports 7,664 bytes of `.text`, 4,536 bytes of `.dynsym`, and
1,824 bytes of `.dynstr`. `nm -D` lists 188 undefined dynamic symbols and no
defined dynamic symbols, while `.rela.plt` is only 408 bytes. This suggests
the retained dynamic symbol inventory is a material size contributor even
though the actual retained code is small; the exact link-owner cause still
needs a current-source linker trace. `.bss` is 526,433 virtual bytes, led by
the 524,288-byte `rt_literal_intern_table`, and does not explain the on-disk
19,912-byte result. `objcopy --strip-unneeded` made no further size reduction.

`readelf -rW` shows 17 PLT relocations and two data relocations in this
artifact. Thus 169 of its 188 undefined dynamic symbols have no dynamic
relocation in the final executable. The trace identifies GNU `ld` at
`/usr/local/bin/ld` as the actual linker. This narrows the size lead to
symbols retained from loaded runtime archive members after section GC; it
does not establish that removing all 169 would save their full `.dynsym` and
`.dynstr` contribution or meet the hard gate.

An `execve` trace of a fresh strict diagnostic build shows the historical
builder invokes clang/ld with `--gc-sections`, five forced roots
(`__simple_runtime_init`, `__simple_runtime_shutdown`, `rt_function_not_found`,
`rt_set_args`, `rt_string_bytes`), the core-C runtime archive, and an empty
strict `_stubs.o`; the archive appears again after that object. It does not
use `--whole-archive` or `--export-dynamic`. The old Rust bootstrap builder
creates an empty `_stubs.o` when strict resolution needs no aliases. The
remaining 188 dynamic imports therefore require archive/object-level
retention analysis rather than a claim that stub definitions cause them.
The trace is `build/mini_builds/target5_strict_core_hello_20260927/execve.log`.

A same-host control under
`build/mini_builds/target5_symbol_retention_20260927/` tests this link behavior.
One archive member held a used function plus an unused `fopen`/`fclose`
function, compiled with `-ffunction-sections -fdata-sections` and linked with
`--gc-sections`. Its stripped executable was 4,400 bytes and still carried
dynamic `fopen` and `fclose` imports. Splitting the functions into separate
archive members made the executable 4,336 bytes and removed both imports;
compiling the combined member with `-flto` did the same. This proves that
section GC alone does not remove those unused imports on this toolchain. It
supports testing object-level runtime splitting or size-mode LTO on the
current-source core-C archive. The control does not prove that either change
alone will satisfy the Simple 15 KiB budget or preserve all runtime behavior.

The current pure-Simple runtime object builder is
`src/compiler/70.backend/backend/runtime_compiler.spl`. It already emits
function/data sections and keys the object cache by its compiler flags. Its
objects feed `link_to_native` through the Stage4 native linker path in
`llvm_native_link_orchestrator.spl`; adding `-flto` at compile time alone
would hand bitcode to a linker path that expects native objects, and changing
flags without changing the cache signature could reuse incompatible objects.
Any LTO experiment must select a compatible link path and version the cache
identity before it can be proposed as a product size fix. Archive-member
splitting remains a separate route, subject to current-source build proof.

## Isolated worktree linker attribution

In `/home/yoon/dev/simple-target56-isolated`, the same historical Stage2
compiler rebuilt strict core-C hello with retained native objects. The GNU ld
link produced a 20,552-byte stripped ELF. Relinking those exact objects and
runtime archive with LLD produced a working 13,944-byte stripped ELF and only
23 dynamic symbols; mold produced 20,552 bytes and 206 dynamic symbols. The
LLD result crosses the absolute 15 KiB diagnostic threshold. Its five runtime
roots, object order, archive order, and `--gc-sections` flags were held fixed.
The native objects are in `.simple/native-objects-MXZNCv`; artifacts are in
`build/mini_builds/target5_iso_core_hello_20260927/`.

A same-host C `puts("hello")` built with clang `-Oz`, `-fPIC -no-pie`,
function/data sections, LLD, section GC, and strip was 4,864 bytes. The
Simple/C size ratio is 2.87,
so the 1.05x gate remains unmet. This comparison is diagnostic because the
Simple build used a historical Stage2 compiler, not an admitted current-source
Stage4 product. The isolated pure-Simple linker source now prefers LLD for
Linux `opt_level == 1` when no explicit `SIMPLE_LINKER` override is set; that
source path still needs a current-source native build and performance proof.

## Linux hello: mmap and literal-print review

The LLD-linked hello ELF imports no `mmap`, `munmap`, or `mprotect` symbol.
Its `.text` is 7,660 bytes, `.dynsym` 552 bytes, and `.rela.plt` 432 bytes.
The 524,288-byte `rt_literal_intern_table` lives in zero-filled `.bss`:
it increases virtual memory size, not ELF file bytes. The host ELF loader's
mapping of LOAD segments is separate from an application `mmap` import, so
deleting an application mmap call cannot explain or repair this file-size gap.

The historical producer boxed `"hello"` with `rt_string_new_literal` and
called `rt_println_value`; its link map retained `rt_to_string` (2,024 bytes)
and the literal table as a result. The isolated current source now lowers a
plain literal passed to `print`, `println`, or `eprintln` to a pointer/length
call into the existing `rt_*print*_str` writer. Cranelift emits a raw rodata
pointer for that typed operand; LLVM already did so. Interpolated values,
computed values, and literals containing NUL keep the prior path. This
removes literal boxing and generic rendering from the simple hello call site.

A same-host C-entry probe called `rt_println_str("hello", 5)` against the same
core runtime archive, with clang `-Oz`, LLD, section GC, and strip. It printed
`hello`, measured 5,152 bytes on disk and 1 byte of `.bss`, and imported no
`mmap`. The probe lives in `build/mini_builds/target5_literal_print_probe/`.
It is 8,792 bytes (about 63%) smaller than the historical 13,944-byte
LLD-linked Simple hello, but the artifacts have different entry points.
It excludes the Simple entry wrapper and the historical builder's forced
runtime roots, so it is directional evidence only. A current-source Stage4
hello build and paired C cohort remain necessary to assess the 1.05x gate.
The attempted pure-Simple `check src/compiler` could not run because there is
no admitted cached self-hosted check worker artifact; the log is alongside
the probe. Do not mark Target 5 complete from this diagnostic.

## Same-wrapper direct-writer diagnostic

A second probe used the historical strict core-C runtime archive, the same
`_main_stub.o` and `_init_all.o`, the same five forced runtime roots, and the
same LLD section-GC link arrangement as the 13,944-byte Simple hello above.
Only the user object changed: a C `spl_main` calls
`rt_println_str("hello", 5)`. It prints `hello` and its stripped ELF is
9,168 bytes (SHA-256
`17f6b463e68e57590a8521e53e1a1a56c0a2a1b0a8684f442e447613d318cfe8`).
The historical Simple ELF is 4,776 bytes larger. The probe reduces `.text`
from 7,660 to 3,316 bytes and `.bss` from 526,433 to 73 virtual bytes;
neither ELF imports `mmap`. The probe source, object, ELF, and link map are in
`build/mini_builds/target5_same_wrapper_probe/`.

This controls the entry wrapper and forced roots, unlike the earlier
5,152-byte C-entry probe. It still uses a C-authored user object, so it is
directional evidence for the literal-print lowering, not a current-source
Simple result. Against the same-host 4,864-byte C `puts` control, the
9,168-byte probe is 1.88x; the 1.05x ceiling is 5,107 bytes, leaving a
4,061-byte gap even for this probe. Its map still retains argv initialization,
array helpers, runtime startup/shutdown, `rt_function_not_found`, and
`rt_string_bytes`. The generated LLVM entry shim unconditionally calls
`spl_init_args`, which also roots argv storage. Removing that call requires
an exact closure proof that neither the program nor a startup hook can read
argv; no such change is admitted here. A current-source Simple artifact and
matched startup/RSS cohorts remain required.

## Forced-root isolation

Using the same C user object, historical entry wrapper, core-C archive, LLD,
section GC, ICF, and strip mode, a diagnostic link without the historical
builder's five forced roots prints `hello` and measures **6,584 bytes**.
Adding only `__simple_runtime_init` and `__simple_runtime_shutdown` as explicit
roots yields the same 6,584 bytes. The wrapper's `rt_set_args` reference
already extracts the runtime member that provides those functions. Relative to
the 9,168-byte five-root probe, the unnecessary `rt_function_not_found` and
`rt_string_bytes` roots therefore account for **2,584 bytes** in this fixture.
The outputs are retained as `direct_print_no_forced_roots` and
`direct_print_required_roots` beside the earlier probe.

The current pure-Simple Stage4 link path derives runtime requests from final
object undefined symbols and does not install the historical five-root list;
its `retained_symbols` list covers explicitly selected external providers.
Therefore deleting five roots from the current linker would not reproduce
this saving. The 6,584-byte diagnostic is still **1,477 bytes** above the
5,107-byte 1.05x C ceiling. It uses the historical wrapper and archive, not a
current-source Simple program, and does not establish a Target 5 pass. The
remaining work is a current-source Stage4 hello link map and an exact
argv/startup/runtime closure analysis before changing their retention policy.

## Startup argv allocation experiment

The historical C bootstrap runtime's `spl_init_args` calls
`simple_runtime_filter_startup_args`, which allocates a filtered argv array
even when no `--startup-extension` argument is present. A local fast-path
experiment reused the original argv on that no-option path and passed the
seven-case C filter probe, including split/equal option forms, `--`
termination, and repeated calls. With the same Clang `-Oz`, LLD, section GC,
and strip flags, the standalone probe grew from **6,576 to 6,728 bytes**
(+152 bytes). The experiment is retained only under
`build/mini_builds/target5_startup_argv_fastpath/`; its source edit was
reverted. The current pure-Simple core's `spl_init_args` already stores argv
directly without allocating this filtered array, so changing the historical
C filter would not reduce the current Stage4 hello footprint. The next size
experiment must use the current-source pure-Simple link closure.

## C-reference reasonableness table

The following is a controlled diagnostic on the same Linux/aarch64 host. The
new pair uses Clang `-Oz -fPIC -ffunction-sections -fdata-sections` for its user
objects and the same historical `_main_stub.o`, `_init_all.o`, core-C runtime
archive, LLD, `--gc-sections`, `--icf=all`, and strip link command for both
binaries. Both print `hello`. The retained inputs and outputs are under
`build/mini_builds/target5_matched_c_pair/`; the direct-writer object is the
previous `target5_same_wrapper_probe/direct_print.o`.

| Binary | Entry and print path | Stripped bytes | Reference | Ratio |
| --- | --- | ---: | --- | ---: |
| Bare C | C `main` calls `puts` | 4,864 | Bare C | 1.000x |
| Historical Simple | Stage2 hello, generic value print, five forced roots | 13,944 | Bare C | 2.867x |
| Historical direct writer | C-authored `spl_main` calls `rt_println_str`, no forced roots | 6,584 | Bare C | 1.354x |
| Matched C | Same startup wrapper and runtime; C `spl_main` calls `puts` | 6,368 | Matched C | 1.000x |
| Matched direct writer | Same startup wrapper and runtime; C `spl_main` calls `rt_println_str` | 6,504 | Matched C | **1.021x** |

The 6,504/6,368 pair passes a 1.05x **matched-startup** threshold (ceiling
6,686 bytes). The same 6,504-byte direct writer misses the current bare-C
threshold (ceiling 5,107 bytes) by 1,397 bytes. This pair controls startup
and link inputs; it does **not** measure a current-source Simple program,
because both user objects were authored in C. Its 80-byte difference from the
earlier 6,584-byte direct writer reflects a different probe link command;
compare only binaries built in the same pair.

Decision: the 15 KiB absolute gate remains meaningful, and the 1.05x ratio is
plausible when C carries the same required startup semantics. The current
bare-C ratio mixes Simple startup and optional extension support into only
one side, so these diagnostics do not justify claiming that its 1.05x target
is reachable. Do not silently change the requirement or cohort checker:
the user must choose the C reference. A current-source Stage4 hello, exact
closure map, and qualified 30/100-sample cohorts are still required before
Target 5 can pass.
