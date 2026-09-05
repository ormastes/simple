# Windows Stage2 SEGV: `/ALTERNATENAME` weak-symbol emulation loses to link
order, so per-module global initializers silently no-op

- **Date:** 2026-08-31
- **Status:** DIAGNOSED, not yet fixed. Refutes the prior "empty-string
  equality is broken in native codegen" hypothesis with direct evidence.

## Symptom (unchanged from prior sessions)

Windows MSVC Stage 2 (`build/w/stage2/x86_64-pc-windows-msvc/simple.exe.rejected`,
108,218,368 bytes) builds and links with zero unresolved symbols and
`--version` works. But any `compile`/parse of even a 2-line hello world SEGVs:

    [build] parse 0/1 step 1/6 +169ms C:/Users/ormas/AppData/Local/Temp/h2.spl
    Segmentation fault      rc=139

## The prior hypothesis, and why it looked plausible

A previous agent's `cdb` breakpoint landed inside `_driver_parse_shard_claim()`
(`src/compiler/80.driver/driver_source_pipeline_parsing.spl:210`) even with
`SIMPLE_PARSE_SHARD` **unset**, when the guard immediately above it should have
short-circuited:

```
fn _driver_parse_shard_owns(path: text) -> bool:
    if _driver_parse_shard_spec() == "":
        return true
    ...
```

Since `_driver_parse_shard_spec()` memoizes into a global (`driver_source_pipeline_parsing.spl:144`):

```
var _driver_parse_shard_memo: text = "@@unset@@"

fn _driver_parse_shard_spec() -> text:
    if _driver_parse_shard_memo != "@@unset@@":
        return _driver_parse_shard_memo
    ...
```

the reachable conclusion was "`text == \"\"` / `!= \"@@unset@@\"` must be
evaluating wrong in native codegen" — a general, severe defect if true.

## What `cdb` actually shows — this is REFUTED

Repro (`cdb -c "g; ln ...; u ...; r; q" simple.exe.rejected compile h2.spl
--format=smf -o h2.smf`, run from a real clone, same crash every time):

```
EXCEPTION_RECORD: c0000005 (Access violation), Attempt to read from address 0000000000000000
...
simple_exe+0x15b469  mov  rax, qword ptr [simple_exe+0x65eb5e0]   ; load global slot
simple_exe+0x15b470  and  rax, 0FFFFFFFFFFFFFFF8h                  ; untag pointer
simple_exe+0x15b474  mov  rcx, qword ptr [rax]                     ; CRASH: rax == 0
```

`rax=0000000000000000` at the fault. `simple_exe+0x65eb5e0` (static VA
`0x1465eb5e0`) was checked against the PE section table
(`llvm-readobj --sections`): `.data` has `VirtualAddress=0x65B8000`,
`RawDataSize=0x31A00` (真正initialized bytes end at `0x65E99A00`), but
`VirtualSize=0xB0EC48` (virtual range extends to `0x116... `). The faulting
address `0x65EB5E0` falls **inside the PE-loader-zero-filled tail of `.data`**
(past `RawDataSize`, still inside `VirtualSize`) — i.e. this global's storage
slot is genuine BSS. It was never written. The crash is a **null-pointer read
of an uninitialized global**, not a text-comparison miscompare: the fault
happens on the pointer *load*, one instruction before any comparison/runtime
call would even run.

This is consistent with `_driver_parse_shard_memo`'s box pointer never having
been populated: the guard code executes, `_driver_parse_shard_memo` is read,
and its slot is null because **the module-level initializer that should have
written `"@@unset@@"`'s heap box into that slot at process startup never ran.**
`SIMPLE_PARSE_SHARD` being unset is irrelevant to this — the crash is upstream
of any env-derived branching, in the global read itself.

## Why the initializer didn't run — the actual mechanism

Per `codegen/llvm/backend_core.rs` (comment at line ~472): "Init-backed globals
are written at startup by `__module_init`" — **even a plain string-literal
`text` global** goes through this path (heap box allocation), not just globals
with a computed initializer. Each module needing this gets a generated
`__module_init[_<prefix>]` function.

The linker's `generate_init_caller`
(`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:849-935`)
scans every compiled object's symbol table via `nm -g`/`llvm-nm`, collects
every `__module_init_*`-prefixed **defined** symbol (minus the
already-called-internally `__module_init_dynamic`), and emits `_init_all.cpp`
which, for MSVC (`is_msvc` branch, lines ~906-923), does this to emulate weak
symbols (MSVC/clang-cl has no `__attribute__((weak))`):

```c
extern "C" { void __module_init_X(void); ... }
#pragma comment(linker, "/ALTERNATENAME:__module_init_X=_X_stub")
extern "C" void _X_stub(void) {}
extern "C" void __simple_call_module_inits(void) {
    __module_init_X();
    ...
}
```

`/ALTERNATENAME:weak=default` tells `link.exe`/`lld-link`: "if `weak` is still
**unresolved** when normal symbol resolution finishes, substitute `default`."
This only does the right thing if the real `__module_init_X` object has
already been pulled into the link by the time that resolution happens.

**Command-line order in `link_objects` (same file) puts `init_o` before the
archive holding the real per-module objects:**

- Lines ~1306-1312 (clang-cl branch): `cmd.arg(&main_o)` then
  `cmd.arg(init)` (i.e. `_init_all.o`, carrying the `/ALTERNATENAME`
  directives) — both added as **direct object-file inputs**, ahead of
  everything else.
- Line ~1384 (inside the `object_paths.len() > 100` branch, Windows-clang-cl
  arm): the archive of every compiled `.spl` module's object code
  (`libspl_objects.a`, containing the REAL `__module_init_<prefix>`
  definitions) is only added via
  `clang_cl_link_args.push(clang_cl_whole_archive_arg(&archive_path))` —
  i.e. `/WHOLEARCHIVE:<archive>`.
- Lines ~1805-1808: `clang_cl_link_args` (the whole-archive flag among them)
  is flushed **once, at the very end**, after a single `/link` group —
  explicitly commented "must follow every compiler argument above."

So the real, final `link.exe`/`lld-link` command line is effectively:

    link.exe  main_o.obj  _init_all.o  [...]  /link  /WHOLEARCHIVE:libspl_objects.a  /FORCE:MULTIPLE,UNRESOLVED  ...

`_init_all.o` — the object carrying the `/ALTERNATENAME` directives — is
processed **before** the whole-archived object that defines the real
`__module_init_<prefix>` symbols. This is a well-documented MSVC-linker
footgun: `/ALTERNATENAME` substitution is order-sensitive, and a weak
reference resolved ahead of the archive that would satisfy it strongly can
silently commit to the alternate (no-op stub) instead of pulling the real
definition in — especially plausible here since nothing else in the link
references `__module_init_<driver_source_pipeline_parsing>` by name (its own
module has no other externally-called symbols that would force that specific
archive member in independently). The result: that module's `__module_init`
body — the code that would allocate `_driver_parse_shard_memo`'s heap box and
store the pointer — silently never executes. The global's storage stays at its
PE-loader-zeroed BSS default: null. First read: null-pointer fault.

This explains the *partial* nature of the failure precisely: most of the
binary works (`--version`, `load_sources`, `source_closure` all run other
modules' globals fine — those symbols may get pulled in "for free" by other
references before ALTERNATENAME resolution, or their globals are statically
representable and skip `__module_init` entirely), while this one module's
initializer is dropped.

## Why this is Windows-only (Unix impact: none)

The non-MSVC branch of the same function (`linker.rs`, the `else` arm around
line ~928) uses a completely different idiom:

```c
extern "C" { void __attribute__((weak)) __module_init_X(void); ... }
extern "C" void __simple_call_module_inits(void) {
    if (__module_init_X) __module_init_X();
    ...
}
```

Real ELF/Mach-O weak symbols are resolved by the dynamic/static linker's own
symbol table with no order dependency of this kind (a weak symbol is
overridden by any strong definition regardless of link order; here the
archive is force-included via `-Wl,--whole-archive` / `-Wl,-force_load`, and
the weak declaration simply becomes non-null once the strong definition is
present). Nothing about this diagnosis or its likely fix touches that branch.
**A fix is a strict improvement — Windows-only, zero surface on Linux/macOS.**

## Fix direction (not applied — needs the ~15min rebuild to verify safely)

Move the archive/whole-archive inputs (or at minimum whatever supplies the
real `__module_init_<prefix>` definitions) to be added to `cmd` **before**
`init_o` in the actual link.exe symbol-resolution order — e.g. either:
(a) emit `_init_all.o` itself via the trailing `/link` group instead of as a
    leading direct object input, so it resolves after the whole-archive, or
(b) keep `/ALTERNATENAME` but additionally force each real
    `__module_init_<prefix>` symbol resolved first via `/INCLUDE:<name>`
    (the code already does this pattern for `security_loader` /
    `runtime_retention_symbols`, see `linker.rs:1497`) for every name in
    `init_names` before the alternate is allowed to apply.
(b) is lower-risk: it doesn't reorder any existing working sequencing, it only
adds one `/INCLUDE:__module_init_X` per discovered name (mirroring the
existing precedent) to force those specific archive members resolved-strong
ahead of the `/ALTERNATENAME` fallback.

## Verification not yet done

Not applied/rebuilt in this session (needs `bash run_s2final.sh`, ~15 min, and
a live retest of `compile`/`native-build` on a hello world reaching step 6/6).
Whoever picks this up: rebuild Stage 2, re-run the `cdb` repro above, confirm
`rax` at `simple_exe+0x15b474`-equivalent is non-null, and confirm hello-world
compiles end to end.

## Update 2026-08-31 (later session): fix (b) applied, measured, REFUTED

Fix direction (b) from above was implemented in `linker.rs` (commit
`a5266266e3d`, "fix(link/msvc): force real __module_init_* resolution ahead
of /ALTERNATENAME"): for every name in `init_names`, when `is_clang_cl`,
`clang_cl_link_args.push(format!("/INCLUDE:{name}"))` is pushed ahead of the
`/WHOLEARCHIVE`-equivalent archive arg, inside the
`object_paths.len() > 100` branch that the real Stage 2 self-build always
takes (818 objects). `cargo check --release --bin simple` was clean, and the
Rust seed was rebuilt with this change in the working tree at the time
(`rust-seed-build.log`, seed timestamp 22:32, after the 22:15 edit to
`linker.rs` and before the 22:51 commit — content-fingerprinted caching means
the seed used in the very next Stage 2 run already carried the fix, confirmed
by `git log -1` on `linker.rs` predating the seed-build timestamp).

**Direct evidence the fix reaches the linker:** re-ran the exact Stage 2
`native-build` command (extracted from
`build/w/stage3/x86_64-pc-windows-msvc/stage2-command.transcript`) by hand
with `--verbose` added, using the freshly-built seed as both the running
binary and `SIMPLE_BINARY`. The captured "Link command:" line contains
**132** distinct `/INCLUDE:__module_init_*` directives, including
`/INCLUDE:__module_init_compiler__driver__source_pipeline_parsing` (the exact
module diagnosed above as never initializing `_driver_parse_shard_memo`).
This is authoritative: it is the actual argv passed to `clang-cl`, not an
inference from source.

**Result: no change, at all, in either build.**

- Binary size: **108,218,368 bytes** — byte-identical to the pre-fix Stage 2
  binary size recorded in this same document and in the two prior builds
  referenced by the handoff note ("byte-identical size (108,218,368) ... same
  SEGV" x2). A real Stage 2 build (`INIT2.log`) and an independent hand-run
  reproduction with `--verbose` (`/tmp/verify_link/simple.exe`) both produced
  this exact byte count.
- Crash: unchanged. Both the real Stage 2 rejected binary and the hand-built
  verbose reproduction SEGV (rc=139) at the same point in the same repro
  (`compile` a 2-line hello world), stopping after the same
  `[build] parse 0/1 ...` log line, before any further build-step output.

Forcing `/INCLUDE:__module_init_<X>` on all 132 names — including the exact
name theorized to be the culprit — measurably reaches `clang-cl`/`link.exe`
and produces a **bit-for-bit identical binary** to the one built without it.
That is only possible if either (a) `link.exe` was already including those
archive members regardless of `/ALTERNATENAME` order (i.e. the "stub wins"
link-order theory in this document is wrong), or (b) `/INCLUDE` has no effect
in this specific configuration (e.g. superseded by `/FORCE:MULTIPLE,UNRESOLVED`
or the `/WHOLEARCHIVE` semantics already forcing every archive member in,
making `/INCLUDE` redundant either way — which would also mean the *original*
diagnosis of "the archive member is never pulled in" needs re-examination,
since a `/WHOLEARCHIVE:libspl_objects.a` should already force-include every
object in that archive, real `__module_init_<prefix>` bodies included, with
or without `/INCLUDE`).

**Fix (b) is REFUTED as the cause of this SEGV.** The `/INCLUDE` directives
are cheap and harmless (confirmed: link still succeeds, symbol table only
grows never shrinks) but do not fix the crash and can stay or be reverted
without effect either way. The uninitialized-global / null-BSS-read
mechanism established via `cdb` disassembly earlier in this document is
still believed accurate; what is refuted is specifically the "ALTERNATENAME
link-order" *explanation* for why that initializer never ran. Root cause is
still open. Next: re-run the `cdb` repro against the current binary to
confirm the same fault address/instruction pattern still reproduces (not yet
done this session — no `cdb`/`gdb`/`windbg` was available in this shell), and
investigate candidate (a) (reorder so the archive precedes `_init_all.o`) or
whether `__module_init_<prefix>` is even being *emitted into the object* for
this module in the first place (i.e. the object never defines the symbol at
all, so no amount of link-order/`/INCLUDE` massaging can help — check via
`llvm-nm` on the specific `driver_source_pipeline_parsing.spl` object file
for a defined `__module_init_compiler__driver__source_pipeline_parsing`
symbol).

## Update 2026-09-01: ROOT CAUSE FOUND AND FIXED — verified end to end

Working through the four questions from the handoff:

1. **Does the module define an init?** Yes. `llvm-nm` on
   `libspl_objects.a` (multiple independent Stage 2 build runs) shows
   `T __module_init_compiler__driver__driver_source_pipeline_parsing`
   consistently DEFINED, and the exact same name appears in the `/INCLUDE`
   directive captured from a real link command
   (`/INCLUDE:__module_init_compiler__driver__driver_source_pipeline_parsing`).
   Both the "never emitted" and "name mismatch" alternate theories are
   REFUTED by this.
2. **Is `__simple_call_module_inits` actually called at startup?** NO —
   and this is the root cause. `compile_main_stub`
   (`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`,
   the `is_msvc` branch, ~lines 761-782) generates a `wmain` that calls
   `__simple_runtime_init()`, `rt_set_args_wide()`, `spl_main()`, and
   `__simple_runtime_shutdown()` — but never declares or calls
   `__simple_call_module_inits()` at all. Compare the non-MSVC `main()`
   stub a few lines below (~802-809), which does call it (guarded by a
   weak-symbol null check). This asymmetry between the two branches is the
   entire bug: `generate_init_caller` always emits a real, callable
   `__simple_call_module_inits` (even MSVC's own `/ALTERNATENAME` branch
   emits a concrete non-weak definition), but nothing on the MSVC path
   ever invoked it. Every module-level global needing a heap-boxed
   initializer (`codegen/llvm/backend_core.rs`, `__module_init[_<prefix>]`)
   silently never ran its initializer on Windows, leaving the global's
   storage at its PE-loader-zeroed BSS default (null) — exactly the `cdb`
   disassembly evidence recorded above.
3. **Init order wrong?** Moot — see (2).
4. **Is the crash really about this global?** Already established via
   `cdb` disassembly earlier in this document; unchanged.

**This also explains why the previous `/INCLUDE` experiment
(commit `a5266266e3d`) was correctly measured as having no effect**: forcing
every `__module_init_*` symbol to resolve strong ahead of `/ALTERNATENAME`
cannot matter when the function that would call any of them (through
`__simple_call_module_inits`) is never invoked in the first place. The
`/ALTERNATENAME` link-order theory this document originally proposed was a
plausible-looking red herring one level removed from the real bug.

**Fix (commit `a833758eb18`):** add the missing declaration and call —
`void __simple_call_module_inits(void);` declared extern and called
right after `__simple_runtime_init()` in the MSVC `wmain`. No
`/ALTERNATENAME` fallback needed for this declaration: `generate_init_caller`
always emits a concrete (non-weak) definition of this specific symbol, even
when `init_names` is empty, specifically to keep the hosted link contract
identical across platforms (see the existing comment at linker.rs:887-891).
Windows-only code path (`is_msvc` branch); the non-MSVC branch is
byte-unchanged, so there is no Unix impact.

**Follow-up fix (commit `88ec90eb472`):** while verifying, found a second,
independent, pre-existing gap: the same MSVC `wmain` stub declares and calls
`rt_set_args_wide(argc, wchar_t** argv)`, which the C runtime never defined
(only the narrow-char `rt_set_args` existed in `runtime_native.c`). Any
native-build output actually linking this MSVC main stub — e.g. the
compiler's own admission smoke test, which builds fixtures with
`--runtime-bundle core-c-bootstrap` — failed at link time with LNK2019
"unresolved external symbol rt_set_args_wide referenced in function wmain".
Added `rt_set_args_wide` to `src/runtime/runtime_native.c` (Windows-only,
`__attribute__((weak))`, mirrors `rt_set_args`): converts each UTF-16 argv
element to UTF-8 via `WideCharToMultiByte` and forwards to the same
`spl_init_args` storage `rt_set_args` uses. Declared in `runtime.h` guarded
by `#ifdef _WIN32`. Verified with `clang -fsyntax-only -target
x86_64-pc-windows-msvc -fms-compatibility -fms-extensions` on
`runtime_native.c`: 0 errors (37 pre-existing warnings, unrelated). Unix
impact: none — entirely inside `#if defined(_WIN32)`.

**End-to-end verification.** Rebuilt Stage 2 with both fixes
(`bash run_s2final.sh`, full Rust seed + Stage 2 native-build, ~13 min).
Result:

- `build/w/stage2/x86_64-pc-windows-msvc/simple.exe` exists (NOT
  `.rejected`) — 108,219,392 bytes. The pre-existing `.rejected` artifact
  from the prior (module-init-fix-only) run was left untouched at its old
  mtime, confirming the sanity/rename path was not triggered this time
  (no rejection occurred).
- `simple.exe --version` → `simple-bootstrap 1.0.0-rc.1`, rc=0.
- `simple.exe compile` on a 2-line hello world (the exact repro that
  previously SEGV'd at rc=139, `[build] parse 0/1 step 1/6` then crash) now
  runs cleanly through `load_sources` → `source_closure` → `parse` →
  `surface_build` → `surface_alias` → `hir`, failing only with a clean,
  legitimate compiler diagnostic (`missing importing module surface for
  ...h2.spl`, rc=1 — an ordinary "no source root configured" condition for
  a bare `compile` invocation without `--entry-closure`/`SIMPLE_LIB`, not a
  crash). **No SIGSEGV. The crash is gone.**
- The Stage 2 native-build itself reported full success in its own log:
  `Build complete: 818 compiled, 0 cached, 0 failed`,
  `Linked: .../simple.exe (105683 KB) via clang-cl`.

**Not fully clean end-to-end — a separate, unrelated infra issue remains**:
the outer `bootstrap-from-scratch.sh` driver reported the stage2 step as
"exit 1" and refused `--stop-after-stage2`'s admission requirement, citing
572 `[native-incremental] cache write skipped ... create cache temp: The
system cannot find the path specified (os error 3)` lines against
`.../stage3/x86_64-pc-windows-msvc/stage2-native-cache/scope-.../objects/.tmpXXXXXX`.
This looks like a directory-creation race in the native-incremental cache
under 12-way parallel compilation (the target `stage2-native-cache/scope-*`
subdirectory not yet existing when the first few workers try to write a
temp file into it) — separate from, and unrelated to, the module-init SEGV
this document tracks. It did not prevent the binary from compiling,
linking, or running correctly, and did not trigger admission rejection
(the `.rejected` rename path is gated on sanity failure specifically, which
never ran here because the driver aborted earlier on this cache-write
condition). Filing separately rather than fixing here to keep this change
narrow; needs its own investigation into
`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs` and
whatever emits `[native-incremental] cache write skipped` (grep that
literal string) plus whether the scope directory is created before or
racing against the first parallel writer.

**Status: module-init SEGV bug in this document is RESOLVED.** Both
commits are on `work/windows-bootstrap-msvc-rebased`, not pushed.
