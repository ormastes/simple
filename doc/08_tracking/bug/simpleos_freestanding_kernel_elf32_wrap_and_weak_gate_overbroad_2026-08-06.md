# SimpleOS freestanding x86_64 kernel: universal ELF32 multiboot wrap + overbroad weak-symbol gate blocked every OVMF/GRUB-EFI board-proxy build — FIXED; a further in-guest rc=70 blocker remains open

- **ID:** simpleos_freestanding_kernel_elf32_wrap_and_weak_gate_overbroad_2026-08-06
- **Status:** Two root causes FIXED and verified (kernel now builds ELF64 and
  passes both host-side gates, boots through L1-L3 under real OVMF pflash). A
  third, downstream, separate blocker remains OPEN: the in-guest
  `/usr/bin/simple /hello.spl` FS-exec run exits `rc=70`. Narrowed (not fixed):
  the process DOES print a diagnostic before exiting (`Runtime error: str.clear
  was called on a receiver that is not text ... receiver=0x0`) — the original
  "no output" observation was a serial-tail-truncation artifact, not the real
  behavior. Root cause is a codegen/runtime dispatch-gap defect in the guest
  interpreter's own parser/lexer frontend, not a kernel/ABI/FS-exec defect. See
  "Root cause #3" below.
- **Severity:** high — was blocking every OVMF-pflash + GRUB-EFI + multiboot1
  x86_64 freestanding kernel build (`ssh_simple_hello_uefi.shs`,
  `ssh_lld_link_uefi.shs`, `build_clang_disk.shs`, `build_fsexec_prod_ring3.shs`),
  i.e. AC-6 of the SimpleOS clang+Simple migration campaign.

## Context / how this was found

AC-6 (install-image contract, proven live via a fresh OVMF boot transcript) was
attempted twice. The first attempt hit `[x86-kernel-elf] ERROR: kernel is not
ELF64` and traced it to `src/os/kernel/fs/fat32.spl` /
`src/os/kernel/ipc/syscall_file.spl` being mid-flight/uncommitted from a
concurrent lane, and correctly declined to fight that edit. That lane has since
landed cleanly (`53e365790554187e5ab696cf79383f4896885b3f`,
`git diff origin/main -- <those two files>` empty). Retrying against the clean
tree reproduced the **exact same** ELF32 failure and the same 56
unbaselined FABRICATED-NEW symbols — proving it was never the FS-lane
collision. Root cause #1 below.

## Root cause #1 (FIXED): unconditional ELF32/EM_386 objcopy downgrade

`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:2291-2318`
(pre-fix). After every successful freestanding x86_64 link with any
`boot_objects` present — which is **every** x86_64 freestanding kernel here,
since `crt0.s` under `<entry-dir>/boot/` is universal — the code unconditionally
ran `objcopy -O elf32-i386` on the just-linked ELF64 kernel, silently
downgrading it to 32-bit `EM_386`.

This downgrade is genuinely required for exactly one caller: the legacy
BIOS/QEMU-`-kernel`-multiboot1 path
(`check-simpleos-wm-fullscreen-evidence.shs`), per the already-filed and
RESOLVED bug
`doc/08_tracking/bug/simpleos_x86_64_kernel_links_as_elf32_em386_2026-07-25.md`
— QEMU's own built-in multiboot loader (used only by direct `-kernel` boot,
not GRUB) mandates ELF32. But the trigger heuristic (`x86_64 + has boot
objects`) is not selective enough: it also fires for the OVMF-pflash +
GRUB-EFI + multiboot1 board-proxy path, whose own gate
(`check-simpleos-x86-kernel-elf.shs`) requires ELF64 — correctly, since
GRUB-EFI's multiboot module accepts ELF64 natively.

Verified directly before attributing: all 325 cranelift-compiled `.o` objects
and the freshly-assembled `crt0.o` are genuinely ELF64/x86-64 (`readelf -h`
sampled and counted: 325/325 ELF64, 0 ELF32). Only the post-link objcopy step
corrupted the class. This previously "worked" (stayed ELF64) only when
`llvm-objcopy` wasn't resolvable on PATH — the code's own fallback path
(`WARNING: objcopy elf32 failed, keeping 64-bit ELF`) kept ELF64 by accident.
An `OBJCOPY_PREFIX` PATH-priming block in `ssh_simple_hello_uefi.shs`, added
for an unrelated reason, made objcopy resolvable, so the downgrade started
firing deterministically.

**Fix:** gated the objcopy step behind a new env var
`SIMPLE_FREESTANDING_ELF32_MULTIBOOT_WRAP=1`, default off (preserves ELF64).
Added the var to the one harness that legitimately needs ELF32
(`check-simpleos-wm-fullscreen-evidence.shs`) and to the other legacy
QEMU-`-kernel` scripts that likely relied on the old default
(`build_fsexec_stream_ring3.shs`, `build_clang_stream_ring3.shs`,
`build_clang_over_ssh.shs`, `ssh_clang_hello_ring3.shs`, `abi_probe_run.shs`),
to avoid silently breaking them. `ssh_simple_hello_uefi.shs` and the other
OVMF/GRUB-EFI scripts (`ssh_lld_link_uefi.shs`, `build_clang_disk.shs`,
`build_fsexec_prod_ring3.shs`) get the correct default (off → ELF64), no
changes needed there beyond what root cause #2 required.

## Root cause #2 (FIXED): weak-symbol gate rejected a legitimate stub-fallback pattern

After #1 was fixed, the kernel linked as ELF64 but `check-simpleos-x86-kernel-elf.shs`
failed with `kernel contains a defined weak symbol`. Traced (not assumed) via
`readelf -sW`: ~40+ `spl_handle_*` syscall-shim symbols (mmap, brk, fork, exec,
file I/O, net, ipc, ...) were defined WEAK. These come from
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`'s "Wave
10B: spl_handle_* weak shims" — deliberate `__attribute__((weak))` C
fallbacks (each just returns `-ENOSYS`(-38) or a minimal bump-allocator
behavior) for syscalls that this particular entry closure
(`ssh_ring3_clang_entry.spl`, an SSH-only kernel) doesn't pull in a Simple
implementation for. Confirmed empirically: `grep -rla spl_handle_mmap
build/os/ssh_simple_cache_uefi128_laneb` found **zero** matches in the
cranelift-compiled object cache — the real Simple implementations in
`src/os/kernel/abi/syscall_shim*.spl` are legitimately not part of this
`--entry-closure` build's reachable module graph, so the weak C stub is the
only definition, exactly as designed.

This is the same class of documented, opt-in incompleteness that
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` already governs for FABRICATED-NEW
symbols in this exact build — the ELF gate just wasn't reading that flag.

**Fix:** `check-simpleos-x86-kernel-elf.shs`'s `validate_symbols` now skips the
defined-weak-symbol check when `SIMPLE_ALLOW_FREESTANDING_STUBS=1` (the
strong-undefined-symbol check is NOT relaxed — a genuinely missing symbol is
still a hard failure). Self-test extended to cover both the strict-default and
opt-in-relaxed paths (`sh scripts/check/check-simpleos-x86-kernel-elf.shs
--self-test` → `simpleos_x86_kernel_elf_self_test=pass`). Callers that build
with `SIMPLE_ALLOW_FREESTANDING_STUBS=1` (`ssh_simple_hello_uefi.shs`,
`build_fsexec_prod_ring3.shs`, `build_clang_disk.shs`) now also pass it to the
gate invocation (previously the flag was scoped to only the `native-build`
subcommand, not exported to the later `sh scripts/check/...` call).

## Verification

```
$ readelf -h build/os/simpleos_ssh_ring3_uefi128_laneb.elf | egrep 'Class|Machine|Type'
  Class:                             ELF64
  Type:                              EXEC (Executable file)
  Machine:                           Advanced Micro Devices X86-64

$ SIMPLE_ALLOW_FREESTANDING_STUBS=1 sh scripts/check/check-simpleos-x86-kernel-elf.shs \
    build/os/simpleos_ssh_ring3_uefi128_laneb.elf
[x86-kernel-elf] PASS: build/os/simpleos_ssh_ring3_uefi128_laneb.elf
```

Fresh `ssh_simple_hello_uefi.shs` run under real OVMF pflash (never `-kernel`):

```
===== UEFI boot ladder =====
  [ok]   L1 OVMF -> GRUB-EFI app ran
  [ok]   L2 multiboot handoff -> kernel _start
  [ok]   L3 sshd ring-3 accept loop
===== exec ladder (serial) =====
  [ok]   L4a sshd deferred exec dispatched
  [MISS] L4b in-guest simple interpreter printed hello
```

Serial log for the exec attempt:

```
[sshd-session] exec command=/usr/bin/simple /hello.spl
[sshd] ring3 deferred heap-stream spawn /usr/bin/simple command=/usr/bin/simple /hello.spl
[fs-exec] heap:stream-open-ok path=/usr/bin/simple len=2300776 hdr_prefix=456
[spawn] stream+heap path=/usr/bin/simple hdr_len=456 file_len=2300776
[spawn] parsed entry=0x1073741824
[spawn] user AS ready (private low) root=402755584
[spawn] PT_LOAD segments mapped
[spawn] entering user cs=0x2b iopl=3 rip=0x1073741824 rsp=0x549757910800
[spawn] ring3 program exited rc=70 (kernel resumed)
[sshd] ring3 deferred heap-stream spawn returned rc=70; accept loop continues
```

## Root cause #3 (NARROWED, still open): dispatch-gap refusal fires with a nil receiver on every script, before any user output

**Update 2026-08-06 (follow-up session):** root-caused far enough to identify
the exact defect *class*, though not yet the single offending call site or a
fix.

### The "no output" framing was wrong

The original report above said rc=70 came "with no crash/fault log line
before the exit." That was a harness artifact, not the truth: the harness's
serial-tail summary (`sed ... | tail -40`) is dominated by post-exit TCP/ARP
noise, which pushed the actual diagnostic line off-screen, and the earlier
pass never grepped for `Runtime error`. The line is there. Full verbatim
transcript, `build/os/ssh_simple_hello_uefi.serial.log` lines 592-607 (fresh
run against a rebuilt kernel + rebuilt `/usr/bin/simple`, host FS-exec path
unchanged from the original report):

```
[spawn] stream+heap path=/usr/bin/simple hdr_len=456 file_len=2305016
[spawn] parsed entry=0x1073741824
[spawn] user AS ready (private low) root=402755584
[spawn] phoff=64 phentsize=56 phnum=7 use_stream=1
[spawn] image span lo=0x1073741824 hi=0x1076224000
[spawn] PT_LOAD segments mapped
[spawn] frame argc readback=2 expected=2
[spawn] user stack mapped top=0x549757911040 pages=2048 rsp=0x549757910800
[spawn] user heap mapped base=0x618475290624 pages=131072
[spawn] entering user cs=0x2b iopl=3 rip=0x1073741824 rsp=0x549757910800
[sc] open path=/hello.spl
[vfs] open /hello.spl -> NVMe read 39 bytes
[simpleos-cpl] phase=post-read cs=0x2b cpl=3
Runtime error: str.clear was called on a receiver that is not text. This
method has no compiled implementation for that receiver type -- a
code-generation dispatch gap, not a program error. Refusing to substitute a
value. receiver=0x0
[syscall] exit status=70
[spawn] ring3 program exited rc=70 (kernel resumed)
```

### `70` is `NOT_FOUND_EXIT_CODE`/dispatch-gap-refusal, confirmed not incidental

`nm bin/release/x86_64-unknown-simpleos/simple` has no `rt_function_not_found`
/ `rt_method_not_found` symbols, so the Rust-runtime abort path
(`src/compiler_rust/runtime/src/value/sffi/error_handling.rs`) is not linked
into this binary — it is compiled purely from `src/compiler` (pure Simple) +
`src/runtime/runtime_native.c` (the C runtime), confirmed via `nm` showing
`compiler__frontend__...`/`compiler__mir_opt__...` symbols and musl-style libc
symbols (`printf`, `simpleos_syscall`, ...). In `runtime_native.c` there are
exactly two `exit(70)` call sites, both inside the single function
`rt_refuse_non_text_receiver(method, receiver)` (originally
`rt_refuse_non_text_receiver(const char* method)`, no receiver arg — see fix
below), called from 8 sites: `rt_reverse`/`rt_reverse_mut` ("rev"/"reverse"),
`rt_take`, `rt_drop`, `rt_string_sorted`, `rt_string_partition_at`, `rt_pop`,
and `rt_clear`. This is the SAME documented dispatch-gap-refusal mechanism as
root cause #2's weak-symbol stubs: `rt_clear`'s dispatch table is keyed on
method NAME only (no receiver type), so any `.clear()` call whose receiver the
compiler could not statically resolve to Array or String reaches this generic
C entry point, and `rt_core_as_array`/`rt_core_as_string` (both reject
`raw < 4096`, i.e. reject nil) refuse it.

### The message names `str.clear`, but the message wording is generic boilerplate

`rt_refuse_non_text_receiver`'s wording always says `"str.%s"` regardless of
what actually failed — it is the fallback for `.clear()` reached with ANY
non-array/non-string receiver, not evidence the call site intended a text
receiver. `simpleos_interpret_file("/hello.spl")` runs
`parse_and_build_module` -> `desugar_module` -> `desugar_collections_static`
-> `HirLowering.lower_module` -> `InterpreterBackendImpl.interpret_hir_module`
before any print, and the compiler's own frontend (parser/lexer) uses the
`X.clear()` idiom pervasively on `[text]`-typed state, e.g.
`src/compiler/10.frontend/core/parser.spl:229-237`
(`if par_errors == nil: par_errors = [] ` then `par_errors.clear()`, same
shape for `par_warnings`, `par_struct_names`) and
`src/compiler/10.frontend/core/lexer_struct.spl:365,375`
(`self.slice_parts.clear()`, field typed `[text]`) and
`src/compiler/10.frontend/core/lexer.spl:743-746`. This fires on a 1-line
`print(...)` script with no input-dependent branching, so whichever call site
is responsible, it fires on EVERY script this interpreter runs — this is not
`/hello.spl`-specific.

### Diagnostic added to discriminate "nil global" vs "mistagged garbage" — result: genuinely nil

Added a `receiver` argument to `rt_refuse_non_text_receiver` so the abort
message prints the raw receiver word
(`src/runtime/runtime_native.c:4074-4082`, all 9 call sites updated to pass
their receiver). Rebuilt: cross-compiled `runtime_native.o` for
`x86_64-unknown-none-elf` with the same flags `src/os/port/llvm/sysroot.shs`
uses, merged into `build/os/sysroot/lib/libsimple_runtime_native.a`, then ran
`scripts/os/simpleos-native-build.shs` (rebuilds
`bin/release/x86_64-unknown-simpleos/simple`, 723 objects, 0 failed) and
reran `ssh_simple_hello_uefi.shs` end-to-end (fresh kernel rebuild too).

Result: `receiver=0x0` — i.e. the value handed to `rt_clear` really is the
untagged integer zero, not a mistagged non-nil pointer/struct (which would
have shown a non-zero hex value that fails `rt_core_as_array`'s `kind`/`cap`
checks instead of its `raw < 4096` early-out). This rules out "wrong-typed but
present" receivers (e.g. an erased Dict/class instance reaching the array/text
dispatch) and narrows the defect to: **the collection this `.clear()` targets
is genuinely absent/uninitialized (0) at the call site**, consistent with
either (a) the module-level `if X == nil: X = []` guard's assignment not
happening before the immediately-following `.clear()` (a nil-guard that
doesn't fire for some other reason), or (b) the guard's assignment happening
but the store not being visible to the very next statement's read of the same
module global under this native/freestanding codegen path — the same general
"module-level global write not observed by an immediately co-located read"
shape as the already-tracked
`reference_jit_module_level_val_from_function_call_reads_zero` family, though
that family is about cross-function calls, not same-function
store-then-immediate-load, so this may be a distinct instance rather than the
same bug.

### Not yet done (deep codegen bug, out of scope for this pass)

- **Which exact `.clear()` call site fires is still unknown.** At least three
  shapes are candidates (module-level `var` in `parser.spl`, a struct field in
  `lexer_struct.spl`, module-level arrays in `lexer.spl`) and they go through
  different codegen paths (module global vs. struct field), so the fix (if
  there is one root cause) is not yet targeted. Pinning this down needs either
  a debug build with call-site-identifying instrumentation (e.g. threading a
  `__LINE__`/site tag into `rt_clear`'s call sites) or single-stepping under
  the kernel's own debug facilities — not done here.
- **No fix landed for the underlying codegen defect.** Only the
  diagnostic (`receiver=` in the error message) is a net-positive, permanent
  improvement — it is generically useful for any future dispatch-gap refusal,
  not a workaround.
- `/usr/bin/simple --version` (which returns at `main.spl:70`, before ever
  touching the parser/lexer) was not tried as a cheaper isolating boot in this
  pass — it would confirm argv/env delivery and process startup are sound
  independent of the parser bug, and is a fast follow-up.

AC-6 (in-guest `/usr/bin/simple --version` + hello-world compile) therefore
**still does not PASS**. What is now proven, not just plausible: L1-L4a
(firmware/kernel/sshd/FS-exec/ELF-load/ring-3-entry) are all sound; the
failure is a codegen/runtime dispatch-gap defect in the guest interpreter's
own frontend (parser/lexer `.clear()` on a collection that reads back as nil),
not a kernel, ABI, syscall, or FS-exec defect.

## Files changed

- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` (root cause #1 fix)
- `scripts/check/check-simpleos-x86-kernel-elf.shs` (root cause #2 fix + self-test coverage)
- `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (opt-in ELF32 wrap preserved)
- `scripts/os/ssh_simple_hello_uefi.shs`, `build_fsexec_prod_ring3.shs`,
  `build_clang_disk.shs` (pass `SIMPLE_ALLOW_FREESTANDING_STUBS=1` through to the gate)
- `scripts/os/build_fsexec_stream_ring3.shs`, `build_clang_stream_ring3.shs`,
  `build_clang_over_ssh.shs`, `ssh_clang_hello_ring3.shs`, `abi_probe_run.shs`
  (opt-in ELF32 wrap preserved for their legacy QEMU `-kernel` boot paths)
- `src/runtime/runtime_native.c` (root cause #3 diagnostic: added a `receiver`
  argument to `rt_refuse_non_text_receiver` and its 9 call sites, so a
  dispatch-gap refusal now prints the actual receiver word — a permanent
  diagnostic improvement, not a workaround; the underlying defect is unfixed)

## PARTIAL — re-verified 2026-08-17 (P2 triage, compiler lane)

The two TITLED defects are fixed at HEAD:

1. The unconditional ELF32/EM_386 objcopy downgrade is now conditional —
   `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:2325-2333`
   (`let want_elf32_multiboot_wrap = ...`).
2. The overbroad weak-symbol gate is now escapable —
   `scripts/check/check-simpleos-x86-kernel-elf.shs:78-96`, with self-tests at
   `:139-143` asserting reject under `SIMPLE_ALLOW_FREESTANDING_STUBS=0` and
   accept under `=1`.

Two record corrections. First, the `file:` field pointing at
`src/compiler/10.frontend/core/lexer.spl` is WRONG: lines 743-746 there are
`lex_snapshot_save`, merely the `.clear()` idiom quoted as an example in this
doc prose, not a defect site. Second, the doc's third symptom (in-guest
`/usr/bin/simple hello.spl` exiting rc=70 on `str.clear` with receiver 0x0) is a
DIFFERENT, still-open defect whose real location is
`src/runtime/runtime_native.c:4535`
`static void rt_refuse_non_text_receiver(const char* method, int64_t receiver)`
— a name-keyed `.clear()`/`rev`/`take`/... dispatch gap that `exit(70)`s on any
unresolved receiver (call sites at `:4585`, `:4623`). The `receiver` diagnostic
argument the doc asked for IS present, so the narrowing landed, but the dispatch
gap itself did not. That third defect should be split into its own record
against `src/runtime/runtime_native.c`, not tracked here.

Also correcting a stale note: `config/simpleos_arm64_servers_weak_undefined_allowlist.sdn`
is PRESENT in the working tree (a deletion of it is staged in another session's
shared index, which is not this lane's change).
