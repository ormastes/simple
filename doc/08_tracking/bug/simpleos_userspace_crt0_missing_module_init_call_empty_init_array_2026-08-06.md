# AC-6 rc=70 root cause pinned: `/usr/bin/simple`'s freestanding crt0 never calls `__simple_call_module_inits` — its `.init_array` is empty, so no heap-backed constant global is ever initialized

- **ID:** simpleos_userspace_crt0_missing_module_init_call_empty_init_array_2026-08-06
- **Status:** OPEN — root cause pinned via host-side binary forensics (no QEMU
  boot required for this pass). No fix landed; the correct fix touches shared
  cross-platform startup code and needs a scoped follow-up, not a same-pass
  patch.
- **Severity:** high — blocks AC-6 (in-guest `/usr/bin/simple` FS-exec) and, by
  the mechanism below, would silently corrupt any freestanding `x86_64-unknown-simpleos`
  binary that reads a `[text]`/`[i64]`/struct-typed module-level constant
  global before ever writing to it.
- **Supersedes the "which `.clear()` call site" framing** in
  `doc/08_tracking/bug/simpleos_freestanding_kernel_elf32_wrap_and_weak_gate_overbroad_2026-08-06.md`
  § "Root cause #3": the exact call site does not matter — **every** module-level
  heap-backed constant global in this binary is uninitialized at boot, so
  whichever one is touched first will trip `rt_refuse_non_text_receiver`
  first. `par_errors`/`slice_parts`/etc. are victims, not causes.

## Method: host-side binary forensics on the exact crashing artifact, no rebuild/boot

The already-deployed `bin/release/x86_64-unknown-simpleos/simple` (mtime
2026-08-06 10:14, i.e. the exact binary the landed lane's QEMU run FS-exec'd
as `/usr/bin/simple` and got `rc=70` from) was still on disk. All of the
following was read directly off it with `readelf`/`nm` — **no new native-build
and no QEMU boot were needed for this pass**:

```
$ readelf -SW bin/release/x86_64-unknown-simpleos/simple | grep -i init_array
  [ 6] .init_array       PROGBITS   00000000401d0200 1d1200 000000 00  WA  0 0  1

$ readelf -sW bin/release/x86_64-unknown-simpleos/simple | grep -E '__init_array_start|__init_array_end'
  6810: 00000000401d0200     0 NOTYPE  GLOBAL DEFAULT    6 __init_array_start
  6811: 00000000401d0200     0 NOTYPE  GLOBAL DEFAULT    6 __init_array_end

$ readelf -sW bin/release/x86_64-unknown-simpleos/simple | grep -c '__module_init'
2   # both hits are the COMPILER'S OWN unrelated source symbols
    # (compiler__backend__backend__llvm_native_link__simpleos_module_init_symbols /
    # ..._module_init_caller_source) -- not runtime-emitted init functions.

$ readelf -sW bin/release/x86_64-unknown-simpleos/simple | grep call_module_inits
(no output)
```

`.init_array` section size is **0 bytes**: `__init_array_start ==
__init_array_end`. `run_init()` (`src/runtime/startup/common/crt_common.c:11-18`)
computes `count = __init_array_end - __init_array_start` and loops
`count` times — with `count == 0` it calls **nothing**. There is also no
`__simple_call_module_inits` symbol anywhere in the binary and zero real
`__module_init_*` functions.

## Control comparison: the SimpleOS kernel ELF, same cranelift backend, same day

```
$ readelf -SW build/os/simpleos_ssh_ring3_uefi128_laneb.elf | grep -i init_array
(no .init_array section at all)

$ readelf -sW build/os/simpleos_ssh_ring3_uefi128_laneb.elf | grep -c '__module_init'
84

$ readelf -sW build/os/simpleos_ssh_ring3_uefi128_laneb.elf | grep call_module_inits
  1735: 00000000080b3a05  1267 FUNC GLOBAL DEFAULT 1 __simple_call_module_inits
```

Same `--backend cranelift`, same day, same repo state, and the kernel binary
has 84 populated module-init functions plus a real, non-empty
`__simple_call_module_inits`. The mechanism plainly works — just not for
`/usr/bin/simple`.

## Root cause: two different crt0s, only one was ever wired for C1

`doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`
§ C1 fixed exactly this class of defect once already (2026-07-17,
"C1 root-fix... LANDED"): module-global initializers weren't running under
freestanding entry-closure builds, fixed by synthesizing
`__module_init_<mod>` functions (`module_global_init.rs` /
`common_backend.rs::generate_module_init`) and an explicit caller
`__simple_call_module_inits` (`linker.rs::generate_init_caller`), wired into
the boot assembly with an **explicit `call`**:

```
# examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:323-328
    .weak __simple_call_module_inits
    ...
    leaq __simple_call_module_inits(%rip), %rax
    ...
    call __simple_call_module_inits
```

That file is the **SimpleOS kernel's own** crt0 — it's what the 84-symbol
kernel ELF above links against.

`/usr/bin/simple` (and any other freestanding `x86_64-unknown-simpleos`
**userspace** binary, i.e. anything built via `native-build --target
x86_64-unknown-simpleos` that isn't the OS kernel image itself) instead links
the **generic baremetal backend crt0**:

```
src/compiler/70.backend/baremetal/x86_64/crt0.s
    _start: ... call check_long_mode / setup_page_tables / enable_paging
            ... call __spl_start_bare      # crt_baremetal.c
```
```c
// src/runtime/startup/baremetal/crt_baremetal.c:50-55
void __spl_start_bare(void) {
    __spl_zero_bss();
    __spl_start(0, (char **)0, (char **)0);   // crt_common.c, shared by
}                                               // baremetal + every hosted
                                                // platform's start.S
```
```c
// src/runtime/startup/common/crt_common.c:41-54
void __spl_start(int argc, char **argv, char **envp) {
    spl_thread_init();
    run_init();                 // walks .init_array ONLY -- no call to
    spl_init_args(argc, argv);  // __simple_call_module_inits anywhere in
    int status = main(argc, argv);   // this file or its callers
    run_fini();
    __spl_exit(status);
}
```

`crt_common.c`'s `__spl_start` is the single shared entry point for
**baremetal, Linux (x86/x86_64/arm64/riscv64), macOS (arm64/x86_64), FreeBSD
(x86/x86_64), and Windows** (`grep -l __spl_start src/runtime/startup/**/*`).
On every one of those platforms it relies solely on `.init_array` actually
being populated and non-empty — which is presumably true for ordinary hosted
`bin/simple` (that binary demonstrably runs and reads its own `[text]`
globals correctly). For the `x86_64-unknown-simpleos` freestanding target
specifically, `.init_array` comes back **empty** in the shipped artifact.

`linker.rs::link_objects_freestanding` (used for both the kernel and
`/usr/bin/simple`, since both target `TargetOS::SimpleOS`) **does**
unconditionally call `generate_init_caller` (line ~1673) — so `_init_all.o`
defining `__simple_call_module_inits` is linked into `/usr/bin/simple`'s
build too, in principle. Nothing in `/usr/bin/simple`'s crt0 chain ever
*references* `__simple_call_module_inits` (unlike the kernel's crt0, which has
an explicit `call`).

**Checked, not assumed, whether `--gc-sections` (confirmed present on the
freestanding link line, both the `lld`-direct and `cc`-driven branches of
`link_objects_freestanding`, `linker.rs:2034` and `:2080`) is what ate the
`.init_array` contents.** It is not — the SimpleOS linker script itself
explicitly protects that section from GC:

```
$ grep -n 'init_array\|KEEP' build/os/sysroot/share/simpleos/simpleos.ld
66:    .init_array : {
67:        __init_array_start = .;
68:        KEEP(*(.init_array .init_array.*))
69:        __init_array_end = .;
```

`KEEP(*(.init_array .init_array.*))` means any input object that placed a
function-pointer into an `.init_array` input section would have survived
`--gc-sections` regardless of whether anything calls
`__simple_call_module_inits`. Since the OUTPUT `.init_array` section is
genuinely 0 bytes (not merely gc'd-to-empty — `KEEP` prevents that), **no
input object ever contributed anything to `.init_array` in the first place**
for this build. So this is not (only) a link-time reachability/gc-sections
story: the cranelift/native-project codegen path apparently never emits an
`.init_array`-attributed data object for `__module_init_<mod>` when targeting
`x86_64-unknown-simpleos`, for reasons this pass did not trace further
(whether that's a cranelift-backend gap vs. a target/linker-script
interaction is exactly the next question — see "Not fixed here" below).
Given `.init_array` was never populated, `--gc-sections` separately explains
why the *function bodies* themselves (`__module_init_<mod>`,
`__simple_call_module_inits`) are also absent from the binary: with no
`.init_array` entry and no crt0 call, nothing references them, so ordinary
(non-`KEEP`) dead-code elimination removes the functions themselves on top of
the already-empty section.

Confirmed (HIR side) that the empty-array shape actually used by `parser.spl`
(`var par_errors: [text] = []`) *does* get an entry in `global_init_arrays`
and would therefore emit a `__module_init_<mod>` body if reached:
`try_const_array_eval` (`hir/lower/module_lowering/module_pass.rs:178-197`)
does `elements.iter().map(element).collect()` on an **empty** `Expr::Array` —
that collects to `Some(vec![])`, not `None` — so
`record_const_array_init` (line 235) inserts a `HirGlobalArrayInit{ values:
vec![], .. }` entry rather than skipping it. So this is not a case of the
empty-literal being (wrongly) treated as needing no runtime init at the HIR
level; the intent to initialize survives to codegen and is then lost only at
the link-reachability step described above.

## Why this explains "fires on EVERY script, before any user output"

Every module-level `val`/`var`/`const`/`static` in the whole ~2.3 MB
`/usr/bin/simple` binary whose initializer is a non-trivial-but-const literal
(any non-empty or empty array/string/struct — anything routed through
`global_init_strings`/`global_init_arrays`/`global_init_functions`/
`global_init_structs`) is, in this build, permanently uninitialized raw zero
bytes at process start. There is no single offending `.clear()` call site;
the first such global anything touches — in this run, `par_errors` inside
`parser_init_with_path` — is whichever one happens to be reached first by
`simpleos_interpret_file`'s startup path. A different entry script that
touched a different global first would crash the same way at a different
line.

## Relationship to prior bug docs — genuinely distinct, not a duplicate

- **Not the same as** `any_slot_holds_untagged_scalar_2026-08-05.md`
  (Any-typed locals stored raw/untagged under the Cranelift **JIT**) — that is
  a value-tagging gap in `Let`/call-arg boxing, observed via `bin/simple run`
  on ordinary hosted Linux. This bug is a **link-time symbol-reachability**
  gap specific to the freestanding userspace crt0, with no tagging or JIT
  involvement — confirmed distinct by a fast host repro: the exact
  `if X == nil: X = []` / `X.clear()` shape from `parser.spl` reproduced as a
  standalone 9-line script (`nilguard_repro.spl`) ran correctly under
  `bin/simple run` (Cranelift JIT, hosted Linux) — `"ok clear passed"` /
  `"done"`, no crash. The JIT path does not go through
  `crt_common.c`/`.init_array` at all (it has its own
  `run_module_init_once`), so this negative result is expected and rules out
  a generic interpreter/codegen store-visibility bug for this exact shape.
- **Not the same as** `any_receiver_element_read_shift_and_tag_2026-08-06.md`
  (reading a typed element off an `any`-typed array param mis-tags/shifts the
  value) — unrelated mechanism (element read casting), also a hosted-JIT
  finding.
- **Same family as, and a second confirmed instance of,** C1 in
  `simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`
  ("module-global initializers never emitted under freestanding
  entry-closure builds") — C1's fix covered the SimpleOS **kernel's own**
  crt0 and the entry-file-wrapping gap; this bug shows the same underlying
  class (module-global runtime init unreachable at boot) still applies to the
  **generic baremetal crt0** used by non-kernel `x86_64-unknown-simpleos`
  binaries, which never received the equivalent explicit-call wiring.

## Not fixed here

`crt_common.c::__spl_start` is shared verbatim by baremetal AND every hosted
platform (Linux x86/x86_64/arm64/riscv64, macOS, FreeBSD, Windows). A naive
fix — add an unconditional `if (__simple_call_module_inits)
__simple_call_module_inits();` call there, mirroring the kernel crt0's
pattern — risks **double-invoking** `__module_init_<mod>` on any hosted
platform where `.init_array` already correctly walks those same functions. If
that assumption is right, a call-initialized global with side effects (e.g.
`var counter = increment_and_get()`) would then run its initializer twice on
those platforms.

**That assumption is NOT verified in this pass, and an attempt to verify it
came back inconclusive/invalid, which matters for anyone picking this up
next.** The only "hosted" native binary available on disk,
`bin/release/x86_64-unknown-linux-gnu/simple`, DOES have a populated
`.init_array` (`INIT_ARRAY`, `0x20` bytes = 4 entries) — but disassembling
those 4 entries shows they are **Rust std/mimalloc/rust-ctor constructors**
(`std::sys::args::unix::imp::ARGV_INIT_ARRAY::init_wrapper`,
`mi_process_attach`,
`simple_runtime::register_static_runtime_symbols_with_abi::__ctor`), not any
`__module_init_<mod>` function — because that binary is the **Rust-seed
compiler itself** (`cargo build` output, confirmed by the seed-warning banner
it prints and by its glibc-dynamic-symbol imports), never built via
`native_project::linker.rs`/`generate_init_caller`/`common_backend.rs::generate_module_init`
at all. It is not a valid comparison for this question. A genuine same-mechanism
comparison needs a **self-hosted pure-Simple AOT native-build for a hosted
target** (e.g. `x86_64-unknown-linux-gnu` via `native-build --backend
cranelift`, no `--target x86_64-unknown-simpleos`), which this pass tried and
could not produce cheaply: `native-build`'s default source-dir resolution
pulled in the full `src/compiler` + `src/lib` tree regardless of `--source .`
pointed at a 9-line standalone repro file (both run from inside the repo and
from `/tmp/spl_repro_native` outside it), and errored out before producing a
binary — a `native-build`-tooling gap in scoping `--source`/`--entry`, not
part of this bug, and not worked around in this pass.

So option 1 vs option 2 below is a **still-open** question, not a settled
call:
1. Make cranelift's data-object emission for `__module_init_<mod>` actually
   register into `.init_array` for the `x86_64-unknown-simpleos` freestanding
   target specifically, so the existing shared `run_init()` path picks it up
   without any crt0 change, or
2. Give freestanding-`SimpleOS`-userspace builds their own crt0 (or a
   target-gated `#ifdef`) that explicitly calls
   `__simple_call_module_inits`, exactly like the kernel's crt0 does, without
   touching the hosted platforms' shared path.

Per this pass's scope (root-cause the AC-6 rc=70 blocker, don't speculative-fix
shared cross-platform startup code), neither is implemented here, and the
double-invoke risk on hosted platforms — the reason a naive `crt_common.c`
one-liner was not attempted — is a plausible but **unconfirmed** hypothesis
pending a valid same-mechanism hosted-AOT comparison binary.

## Files/artifacts referenced (no source changed this pass)

- `bin/release/x86_64-unknown-simpleos/simple` (the crashing artifact,
  inspected via `readelf`/`nm`, not rebuilt)
- `build/os/simpleos_ssh_ring3_uefi128_laneb.elf` (control comparison)
- `src/runtime/startup/common/crt_common.c` (shared `__spl_start`/`run_init`)
- `src/runtime/startup/baremetal/crt_baremetal.c` (`__spl_start_bare`)
- `src/compiler/70.backend/baremetal/x86_64/crt0.s` (userspace freestanding
  entry, no `__simple_call_module_inits` call)
- `examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:323-328` (kernel's
  own entry, has the explicit call — the working precedent)
- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:822-945`
  (`generate_init_caller`), `:1673` (unconditional call site in
  `link_objects_freestanding`)
- `src/compiler_rust/compiler/src/codegen/common_backend.rs:2228+`
  (`generate_module_init`, ".init_array" registration comment)
- `src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:178-197,224-270`
  (`try_const_array_eval`/`record_const_array_init` — confirms empty-array
  globals DO get a `global_init_arrays` entry, ruling out an HIR-level
  no-init-needed shortcut)
- `doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`
  § C1 (prior, related, partially-overlapping fix)
- `doc/08_tracking/bug/simpleos_freestanding_kernel_elf32_wrap_and_weak_gate_overbroad_2026-08-06.md`
  § "Root cause #3" (this doc supersedes that section's "which call site"
  framing with a link-reachability root cause)
- `doc/08_tracking/bug/any_slot_holds_untagged_scalar_2026-08-05.md`,
  `doc/08_tracking/bug/any_receiver_element_read_shift_and_tag_2026-08-06.md`
  (related but confirmed-distinct JIT/tagging bugs, cross-linked above)
