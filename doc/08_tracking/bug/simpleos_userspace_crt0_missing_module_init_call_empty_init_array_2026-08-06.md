# AC-6 rc=70 root cause pinned and FIXED: `/usr/bin/simple`'s freestanding crt0 never called `__simple_call_module_inits` — its `.init_array` is empty, so no heap-backed constant global was ever initialized

- **ID:** simpleos_userspace_crt0_missing_module_init_call_empty_init_array_2026-08-06
- **Status:** FIXED — `src/os/libc/simpleos_crt0.S` now calls
  `__simple_call_module_inits` (weak-guarded) before `main`, verified by a
  real end-to-end QEMU-user-mode sabotage test (pre-fix reproduces the bug,
  post-fix fixes it — see "Fix landed" below). The double-invoke risk that
  blocked the first pass does not apply: the actual fix locus,
  `src/os/libc/simpleos_crt0.S`, is a SimpleOS-only file never linked into
  any of the 7 other (hosted) platforms — see "Correction" below for why the
  first pass's proposed fix locus was wrong.
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

## Correction (2026-08-06, follow-up pass): the crt0 file this doc named is not the one actually linked into `/usr/bin/simple`

The first pass's file-chain claim —
`src/compiler/70.backend/baremetal/x86_64/crt0.s` →
`src/runtime/startup/baremetal/crt_baremetal.c` → `crt_common.c` — was
plausible from source reading alone but turned out to be **the wrong crt0**
for this specific artifact. Traced from the actual linker decision instead of
from source-tree browsing:

- `native_project::linker.rs::link_objects_freestanding` computes
  `has_simpleos_crt0 = simpleos_user_runtime_paths(cross_target).is_some()`
  (`linker.rs:2221`). For `TargetOS::SimpleOS` + `TargetArch::X86_64`,
  `simpleos_user_runtime_paths` (`linker.rs:207-225`) requires
  `sysroot/lib/crt0.o` + `libsimple_runtime.a` + `libsimpleos_c.a` to all
  exist, and when they do, that `crt0.o` is what gets used as the link's
  actual entry object — **not** the generic
  `src/compiler/70.backend/baremetal/x86_64/crt0.s`.
- `src/os/port/llvm/sysroot.shs:117` installs `sysroot/lib/crt0.o` by
  copying `$LIBC_DIR/simpleos_crt0.o` — which is assembled from
  **`src/os/libc/simpleos_crt0.S`**, a completely different file, owned by
  the SimpleOS libc shim (`src/os/libc/`, which also builds
  `libsimpleos_c.a` per `src/os/libc/Makefile`).
- `simpleos_crt0.S`'s `_start` calls `__libc_init_array` (defined in
  `src/os/libc/simpleos_cxxabi.c:234-241` — a **separate, from-scratch**
  `.init_array` walker, not `crt_common.c::run_init`, though functionally
  identical: same empty-`.init_array` gap applies to it), then calls `main`
  directly. It never went through `crt_common.c`/`__spl_start`/
  `__spl_start_bare` at all — those symbols are irrelevant to this specific
  binary's boot path. The original three-file chain this doc named is real
  code (it's what a *different* class of freestanding baremetal build, e.g.
  a raw multiboot2 kernel without an OS-provided loader, would use) but is
  simply never reached for `x86_64-unknown-simpleos` **userspace** links that
  have a populated sysroot, which `/usr/bin/simple`'s build does.

This actually **strengthens** rather than weakens the root-cause finding
(same empty-`.init_array`, same "no explicit call anywhere" mechanism, same
symptom) — it only changes which file needs the fix.

## Fix landed: `src/os/libc/simpleos_crt0.S`

Added a weak-guarded call to `__simple_call_module_inits` between
`__libc_init_array` and `main`, exactly mirroring the pattern the SimpleOS
kernel's own crt0
(`examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:323-328`) and the
hosted-platform generated main() stub
(`native_project/linker.rs::compile_main_stub`, the
`if (__simple_call_module_inits) __simple_call_module_inits();` line) both
already use:

```asm
    call    __libc_init_array
    lea     rax, [rip + __simple_call_module_inits]
    test    rax, rax
    jz      .Lmodule_inits_done
    call    rax
.Lmodule_inits_done:
    /* Call main(argc, argv, envp) */
```

plus `.weak __simple_call_module_inits` alongside the file's other weak
forward references (`__bss_start`/`__bss_end`/`rt_set_args`), so a link with
no module-init functions to aggregate (nothing routed through
`generate_init_caller`) still resolves cleanly, same as those.

### Why this is safe re: the double-invoke risk that blocked the first pass

The first pass's concern was specific to `crt_common.c::__spl_start`, which
**is** genuinely shared by baremetal and all 7 hosted platforms (Linux
x86/x86_64/arm64/riscv64, macOS, FreeBSD, Windows) — confirmed by `grep -rl
__spl_start src/runtime/startup/`. That file was **not touched** by this fix.

The actual fix locus, `src/os/libc/simpleos_crt0.S`, is architecturally
isolated from every hosted platform, verified two ways, not assumed:

1. **Directory/ownership**: `src/os/libc/` is the SimpleOS libc shim
   (`simpleos_libc.c`, `simpleos_fs.c`, `simpleos_process.c`, etc.) —
   entirely SimpleOS-specific, never built for hosted targets.
2. **Reachability**: `grep -rl __spl_start_bare src/runtime/startup` (the
   symbol this doc originally worried about) returns only baremetal files;
   `simpleos_crt0.S` doesn't even call that symbol — it calls `main`
   directly, a completely separate code path from any hosted platform's
   `start.S` → `crt_common.c::__spl_start` → (hosted `main()` stub, which
   already explicitly calls `__simple_call_module_inits` once, per
   `compile_main_stub`).

So there is no code path, on any of the 8 platforms, that would now call
`__simple_call_module_inits` twice as a result of this change.

### Empirical end-to-end verification (real crt0.S, real qemu-x86_64 execution, not a mock)

Rather than relying on static reasoning alone, built a real sabotage test
using the **actual** `src/os/libc/simpleos_crt0.S` (both pre- and post-fix
versions) linked against a mock `main`/`__libc_init_array`/
`__simple_call_module_inits`/`__module_init_*` object (mirroring
`generate_init_caller`'s emitted shape) and a module-level global flag, run
under `qemu-x86_64` (user-mode emulation, real syscalls):

```
$ qemu-x86_64 pre_fix.elf     # unmodified simpleos_crt0.S (git show HEAD:...)
GLOBAL_NOT_READY_BUG

$ qemu-x86_64 post_fix.elf    # fixed simpleos_crt0.S
MODULE_INIT_RAN
GLOBAL_WAS_READY_IN_MAIN
```

Confirms: (a) the bug reproduces exactly as diagnosed with the unmodified
crt0 — the module initializer never ran, so `main` observed the global as
never-initialized; (b) the fix resolves it — the initializer runs before
`main` and the global is observed ready. Also confirmed via `objdump -d` that
the compiled call sequence is `__libc_init_array` → weak-guarded
`__simple_call_module_inits` → `main`, matching the source.

### Still open / follow-up

- `src/os/libc/simpleos_crt0_aarch64.S` (the aarch64 counterpart) was not
  touched — the same gap likely applies there and needs the equivalent fix;
  out of scope for this pass (task scope was the x86_64 AC-6 blocker).
- The deeper "why does cranelift never populate `.init_array` for this
  target" question (option 1 in the original writeup) remains unanswered and
  is now redundant to fix given this crt0-level fix, but would still be worth
  understanding if `.init_array` is relied on for anything else on this
  target.
- If `.init_array` population for this target is ever separately fixed later
  (option 1), this crt0 call and that would together double-invoke module
  inits — whoever does that fix must remove this call or make
  `__simple_call_module_inits` self-guard against re-entry.
- Not yet re-verified via a full real `/usr/bin/simple` rebuild + QEMU-system
  boot (the actual AC-6 FS-exec scenario) — that requires rebuilding
  `sysroot/lib/crt0.o` (`sh src/os/port/llvm/sysroot.shs` or equivalent) and
  re-running the SimpleOS-native-build + QEMU FS-exec harness end to end,
  which is a substantially longer-running verification than this pass's
  qemu-user-mode sabotage test and was not run here. The sabotage test above
  demonstrates the mechanism is correct on the exact source file that will be
  linked; the full-system re-run is the recommended final confirmation before
  closing AC-6 itself.

## Files/artifacts referenced

- `bin/release/x86_64-unknown-simpleos/simple` (the crashing artifact,
  inspected via `readelf`/`nm`, not rebuilt this pass — see "Still open")
- `build/os/simpleos_ssh_ring3_uefi128_laneb.elf` (control comparison)
- `src/os/libc/simpleos_crt0.S` — **fix landed here**: weak-guarded
  `__simple_call_module_inits` call before `main`
- `src/os/libc/simpleos_cxxabi.c:234-241` (`__libc_init_array`, the
  from-scratch `.init_array` walker this crt0 actually uses — separate from
  `crt_common.c::run_init`)
- `src/os/port/llvm/sysroot.shs:117` (installs `sysroot/lib/crt0.o` from
  `simpleos_crt0.S` — traces why this is the real fix locus)
- `src/runtime/startup/common/crt_common.c`, `src/runtime/startup/baremetal/crt_baremetal.c`,
  `src/compiler/70.backend/baremetal/x86_64/crt0.s` — the file chain the
  first pass named; confirmed NOT the one linked into this artifact, but
  real code used by a different class of freestanding baremetal build (see
  "Correction")
- `examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:323-328` (kernel's
  own entry, has the explicit call — the working precedent this fix mirrors)
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
