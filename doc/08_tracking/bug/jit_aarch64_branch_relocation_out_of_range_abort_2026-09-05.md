# `bin/simple` aborts intermittently: AArch64 JIT branch relocation out of ±128 MB range

**Filed:** 2026-09-05
**Severity:** medium — non-deterministic abort of any JIT-executed tool invocation on aarch64
**Status:** **FIXED 2026-09-06** (see the final section). History below is kept:
it records what was measured while the cause was still open, including two
hypotheses that were tested and falsified.
**Area:** Rust seed JIT (`codegen::jit`) over vendored `cranelift-jit`

## What happened

While exercising `bin/simple fmt` on small scratch files, one invocation died
with SIGABRT (rc=134) and another with SIGSEGV, on inputs that exit 0 when
re-run. The abort left a crash report:

```
Message:  assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)
Location: src/compiler_rust/vendor/cranelift-jit/src/compiled_blob.rs:90:21
OS:       linux aarch64
   8: <cranelift_jit::backend::JITModule>::finalize_definitions
   9: <simple_compiler::codegen::jit::JitCompiler>::compile_module
  10: <simple_compiler::codegen::local_execution::LocalExecutionManager …>
  11: <simple_driver::exec_core::ExecCore>::run_file_jit
  15: simple::dispatch_to_simple_app
```

`diff >> 26` is the range check for the AArch64 26-bit signed branch immediate
used by `B`/`BL` (`CALL26`/`JUMP26` relocations): ±128 MB. The assertion fires
when the JIT resolves a call whose target landed further than that from the
call site, i.e. when the JIT's code allocations are spread too far apart in the
address space.

## Why it is intermittent

The failure depends on where `mmap` places the JIT code regions, not on the
input. That is consistent with what was observed: identical inputs abort under
memory pressure (a large concurrent `native-build` was running) and exit 0 when
re-run on a quieter box. It is a latent defect, not a flake — the same
invocation can abort at any time, and the larger the JIT-compiled module the
more likely it is.

`bin/simple` JIT-compiles the tool being dispatched, so this can abort **any**
tool invocation (`fmt`, `lint`, `run`, …), not just the one observed.

## Evidence and scope

- Binary: `bin/simple` -> `bin/release/aarch64-unknown-linux-gnu/simple`
  (154,560,904 bytes, 2026-09-04 14:46) — the Rust seed.
- Crash report: `.simple/logs/crash_1508768.log` (directory is gitignored).
- 1 of the 10 crash reports present carries this assertion. The other 7 (dated
  2026-09-04) carry a different message, `can't resolve symbol
  text_dot_from_char_code`, which looks like the known unbacked-extern class
  (`unregistered_extern_silent_nil_2026-08-01.md`) rather than this one, and is
  not analysed here.

## Not fixed here

The failing assertion is in vendored code
(`src/compiler_rust/vendor/cranelift-jit/**`), which is outside the owned-code
scope, and the real fix belongs on our side of the boundary anyway: the JIT
should either allocate code regions within branch range of each other, or
emit far-call veneers / a PLT-style thunk when a target is out of ±128 MB.
Choosing between those is a design decision, so it is recorded rather than
guessed at.

## Reproduction note

No deterministic reproducer. Suggested approach: run a JIT-executed tool under
memory pressure or with ASLR forcing distant mappings, on a module large enough
to need multiple code allocations. A targeted alternative is to assert in
`JitCompiler::compile_module` that all code regions land within 128 MB and see
how often that is violated in normal runs.

## Second and third observations (2026-09-05, SOSIX unification lane)

`bin/simple lint src/lib/nogc_async_mut/sosix/file_driver.spl` (87 lines) dumped
core with the same `assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)`
(`.simple/logs/crash_2422254.log`, `JitCompiler::compile_module` via
`ExecCore::run_file_jit`), and `bin/simple lint src/lib/nogc_async_mut/sosix/fs.spl`
(276 lines) aborted the same way on its second run after reporting
`NOT LINTED: 1 file(s) could not be parsed` on its first. `lint sync.spl` in
between passed. Same binary: `bin/release/aarch64-unknown-linux-gnu/simple`,
2026-09-04 14:46. So it reproduces on demand under `lint` of these files, and
`--mode=interpreter` does not avoid it (both files dumped core again:
`crash_2425695.log`, `crash_2425892.log`). No lint verdict is obtainable for
these two files on this host until the seed is fixed; the lane records them as
**not linted**, not as clean.

## Deterministic reproducer (2026-09-06)

The 2026-09-05 entry said "observed once, not reproduced on demand". It now
reproduces on every run:

```
SIMPLE_LIB=src VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json \
  VK2D_W=800 VK2D_H=600 VK2D_RECTS=64 VK2D_FRAMES=300 \
  src/compiler_rust/target/vulkan/release/simple run \
  test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl
```
-> `timeout: the monitored command dumped core`, crash log
`Message: assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)` at
`vendor/cranelift-jit/src/compiled_blob.rs:90`, via
`JITModule::finalize_definitions` <- `JitCompiler::compile_module` <-
`ExecCore::run_file_jit`.

This is a bigger JIT module than `fmt` on a scratch file, which matches the
original note that "the larger the JIT-compiled module the more likely it is" —
past some size it is not probabilistic any more, it is certain.

**Consequence beyond tooling:** this is what blocks
`scripts/check/check-vulkan-2d-c-compare.shs` from ever producing a Simple-leg
number. With the gate's platform assumptions fixed the C leg now measures
(`c-vulkan-2d ... fps=10272.0`), and the Simple leg dies here. So the
Simple-vs-C 2D perf gap cannot be measured on aarch64 until this is fixed.

## Corrected root-cause analysis

`src/compiler_rust/compiler/src/codegen/common_backend.rs` (`BackendSettings::jit()`)
sets `is_pic = cfg!(target_arch = "x86_64")` and explains it as:

> PLT entries needed by is_pic=true are only implemented for x86_64 ...
> On aarch64/riscv/etc., disable PIC so the assert never fires.

**That reasoning is inverted for this defect.** There are two different asserts:

| setting | aarch64 path | assert |
|---|---|---|
| `is_pic = false` (current) | direct `BL`, `Reloc::Aarch64Call` | `compiled_blob.rs:90` range check — **the one we hit** |
| `is_pic = true` | needs a PLT stub | `backend.rs:296` `"PLT is currently only supported on x86_64"` |

Disabling PIC does not avoid an assert; it *chooses* this one. The comment
should say so, otherwise the next reader concludes aarch64 is already safe.

## Workaround: `SIMPLE_EXECUTION_MODE=interpret` (2026-09-06)

The line above saying "`--mode=interpreter` does not avoid it" is **wrong, and
the experiment behind it did not test what it claimed**. `--mode=interpreter`
is not a flag `run` accepts; it is consumed as a FILE PATH:

```
$ simple run --mode=interpreter <file>
[INFO] JIT compilation failed, falling back to interpreter: module load error:
       io: Cannot read "--mode=interpreter": No such file or directory
error: compile failed: io: Cannot read "--mode=interpreter"
```

So that run never selected the interpreter — it passed an unrecognised argument
and then JIT-compiled the real file as usual, which is why it still aborted.

The switch that works is the environment variable read at
`driver/src/exec_core.rs:223`, whose accepted values are `jit` |
`interpret` | `interpreter` | `interpret-optimized`:

```
SIMPLE_EXECUTION_MODE=interpret simple run <file>
```

Positive control: a hello-world runs identically under the default and under
`interpret`. On the vk2d_bench reproducer the JIT lane dumps core in seconds
while the interpreter lane produces **no crash log at all**.

**How far it actually gets, measured — do not overstate this.** At the gate's
own size (800x600, 64 rects, 300 frames) it did NOT finish: killed at the 900 s
timeout with no fps line. Shrunk to 64x64 / 1 rect / 1 frame it completes and
emits a real result:

```
simple-vulkan-2d w=64 h=64 rects=1 frames=1 readback=true ms=48 fps~=20
  draw_us=1217 batch_us=2083 present_us=38569 readback_us=7045
```

So `interpret` is a correctness escape hatch — it proves the Simple 2D lane
works and yields per-stage numbers — but it is far too slow to stand in for the
JIT/native lane in `check-vulkan-2d-c-compare.shs`. That gate still cannot
produce a Simple leg until the JIT defect is fixed.

## Three states measured 2026-09-06 (the cheap fixes are ruled OUT)

Each row was built and run against the deterministic reproducer above. This
supersedes the "just flip is_pic" reading that the earlier text invited.

| # | configuration | result |
|---|---|---|
| 1 | `is_pic=false` (current tree) | `compiled_blob.rs:90` CALL26 range assert — the shipped symptom |
| 2 | `is_pic=true`, stock vendor | aborts at once: `PLT is currently only supported on x86_64` (`backend.rs:297`) |
| 3 | `is_pic=true` + an aarch64 PLT stub added to the vendored crate | PLT assert gone; **back to the `compiled_blob.rs:90` CALL26 assert** |

State 3 is the important one. An aarch64 PLT stub
(`adrp x16 / ldr x16, [x16] / br x16`, 12 of the 16 available bytes, x16 being
the AAPCS64 inter-procedural scratch register) builds and removes the
x86_64-only limitation — but it is **necessary and not sufficient**. `is_pic`
governs how *external* symbols are referenced; calls between functions defined
in the same JIT module still lower to a direct `BL`/CALL26, and those are what
overflow once the JIT's code regions are more than 128 MB apart.

So the fix cannot be a relocation-*kind* change. It has to be one of:

- **veneers/islands** — in the `Reloc::Aarch64Call` arm of `compiled_blob.rs`,
  when `diff` does not fit in 26 bits, emit a trampoline within range that does
  the full 64-bit `adrp`/`ldr`/`br` and retarget the `BL` at it. This is what a
  real linker does for long branches; it is the standard answer.
- **bounded code allocation** — reserve one contiguous region up front and
  allocate every JIT blob inside it, so the displacement can never exceed
  +/-128 MB. Simpler, but caps total JIT code size.

**A trap for whoever does this.** `src/compiler_rust/vendor/` is wired in by
`.cargo/config.toml` (`[source.crates-io] replace-with = "vendored-sources"`),
so edits there DO reach the build — but cargo treats vendored crates as
immutable. Editing a file silently changes nothing: three consecutive builds
reported `Finished in ~1.3s` with the old code still linked, and
`cargo clean -p cranelift-jit` removed 0 files. To actually rebuild you must
(a) update that file's hash in `vendor/cranelift-jit/.cargo-checksum.json`, and
(b) delete `target/**/deps/libcranelift_jit-*.{rlib,rmeta}` and
`target/**/.fingerprint/cranelift-jit-*`. Verify with
`strings <binary> | grep 'PLT is currently only supported'` — if the string is
still present, your patch is not in the binary no matter what cargo printed.

## Concrete fix path

`Reloc::Aarch64AdrGotPage21` and `Aarch64Ld64GotLo12Nc` are **already
implemented** for aarch64 in `compiled_blob.rs` — GOT addressing works. The only
missing piece is the PLT stub in `backend.rs::write_plt_entry_bytes`, which is
hardcoded to x86_64. An aarch64 stub fits the existing 16-byte entry:

```
adrp x16, <got page>      ; page of the GOT slot
ldr  x16, [x16, #<lo12>]  ; load target
br   x16                  ; tail-call it
```

12 bytes of the 16 available, and `x16` (IP0) is the architecturally reserved
inter-procedural scratch register, so clobbering it across a call is legal.
That was the original hypothesis. It was TESTED on 2026-09-06 and is wrong:
see state 3 in the table above — local JIT-to-JIT calls stay direct, so the
displacement problem survives.

**Not done here** because `vendor/cranelift-jit/**` is vendored third-party code
and CLAUDE.md scopes it out; this needs an explicit decision to patch vendor (or
to carry the change upstream). Filed with the reproducer so that decision can be
made on evidence.

## FIXED 2026-09-06 — and the abort was only half of it

Two defects, both in vendored `cranelift-jit` 0.116.1, both now patched
(`src/compiler_rust/vendor/cranelift-jit/`).

### Defect 1 — the range check is one bit too loose (silent miscompile)

`compiled_blob.rs`'s `Reloc::Arm64Call` arm asserted

```rust
let diff = ((base as isize) - (at as isize)) >> 2;   // words
assert!((diff >> 26 == -1) || (diff >> 26 == 0));    // admits +/-2^26 words
```

but `imm26` is a **signed 26-bit word** offset, so the encodable range is
`[-2^25, 2^25)` words = +/-128 MiB — matching cranelift-codegen's own
`LabelUse::Branch26 => (1 << 27) - 1` *bytes*
(`vendor/cranelift-codegen/src/isa/aarch64/inst/mod.rs:2901`). The assert
therefore admitted displacements up to +/-256 MiB; anything in the 128..256 MiB
band **passed the assert and was then truncated into a branch to a completely
wrong address**. That is why the primary reproducer here dies with SIGSEGV in
JIT code (`pc` inside a JIT mapping, garbage `x30`) rather than with the
documented SIGABRT: the abort is the *lucky* outcome, the SEGV is the same root
cause landing one bit further out. The check is now `diff >> 25`.

### Defect 2 — JIT code pages are handed out by the process allocator

`memory.rs`'s `PtrLen::with_size` uses `std::alloc::alloc`, which mixes
brk-heap and mmap'd blocks; on this host they land gigabytes apart, so two
functions of the *same* JIT module could not reach each other with a `bl`.

Fix: the *code* `Memory` of every `JITModule` (`Memory::new_code`, wired at
`backend.rs:531`) is now backed by one contiguous `mmap` reservation of exactly
`2^27` bytes — exactly the reach of a `bl` — so any two addresses inside it are
in range **by construction**. The reservation is lazy and `MAP_NORESERVE`, so an
unused module costs only address space; measured high-water mark for the vk2d
bench is **7,284 KiB of 131,072 KiB** (`SIMPLE_JIT_ARENA_STATS=1`).

Long-branch veneers (`ldr x16, #8 ; br x16 ; .quad target`, the standard
BTI-safe PLT thunk shape) are carved downwards from the top of the same arena
and cover a colocated target that lands outside it. `SIMPLE_JIT_FORCE_VENEERS=1`
routes *every* `Arm64Call` through a veneer so the path is exercised rather than
dead: the vk2d bench runs clean that way with 10,155 veneers installed.

**Stated cap:** 128 MiB of JIT code per `JITModule`. Beyond it the allocator
warns once and falls back to the old heap path, where the hazard returns — but
now with a descriptive panic naming this document instead of a bare assert.

### Before / after (same host, same build flags, aarch64)

Reproducer: `SIMPLE_LIB=src VK2D_W=800 VK2D_H=600 VK2D_RECTS=64 VK2D_FRAMES=300
simple run test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl`, seed built with
`--features vulkan`.

| binary | runs | failures |
|---|---|---|
| unpatched | 8 | **2** — one `rc=139` SIGSEGV, one `rc=124` (spun at 99% CPU for the full 900 s timeout after `scene_source=table rects=64`, i.e. a corrupted branch target turned into an infinite loop) |
| patched | 8 | **0** |
| patched, `SIMPLE_JIT_FORCE_VENEERS=1` | 3 | **0** (10,155 veneers installed per run) |

`.simple/logs/crash_*.log` count went 5 -> 5 across every patched run; all five
existing reports are from unpatched runs and every one of them carries exactly
`assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)` at
`compiled_blob.rs:90`, i.e. the assert in this report. The SIGSEGV and the hang
are the *same* defect landing in the band the assert failed to catch.

Common-path regression check: `simple run` on `hello_native.spl` plus three
mid-size examples produces **byte-identical output** on the unpatched and
patched binaries, and `lint src/lib/nogc_async_mut/sosix/fs.spl` x5 adds no
crash report (it still exits 1 on a pre-existing semantic error, unchanged).

The failure is ASLR-dependent: under `gdb` with its default
`disable-randomization on` the unpatched binary does **not** crash, which is why
the original report could not reproduce on demand.

### Superseded 2026-09-06 (was: "Still red, and NOT caused by this bug")

This section previously reported that
`scripts/check/check-vulkan-2d-c-compare.shs` was skipped because this host has
no `vulkan/vulkan.h`, and that the Simple leg was blocked because
`vulkaninfo --summary` listed 20 instance extensions with `VK_KHR_surface`
**not** among them. **Both claims are now falsified.** They are kept here rather
than deleted because the second one was used as a reason to stop looking.

- **The C leg builds.** The header probe only looked at
  `/opt/homebrew/include/vulkan/vulkan.h` (macOS), `clock_gettime` was hidden by
  glibc under `-std=c99` without `-D_POSIX_C_SOURCE=199309L`, and only
  `libvulkan.so.1` exists here, not `libvulkan.so`. Fixed in PR #401; the C leg
  measures.
- **`VK_KHR_surface` is present.** `vulkaninfo --summary` lists 21 instance
  extensions **including `VK_KHR_surface` revision 25** and
  `VK_EXT_headless_surface`. What is genuinely absent is `VK_KHR_xlib_surface` /
  `VK_KHR_wayland_surface`, and those are gated on loader availability by the
  fix in PR #400 (`src/compiler_rust/runtime/src/vulkan/instance.rs:155-210`).
  The earlier `ERROR_EXTENSION_NOT_PRESENT` came from a seed built *before* that
  fix, not from a missing extension.

Re-measured on a seed rebuilt with `--features vulkan`: `VulkanSession.init()`
returns `code=0`, `VulkanBackend.create().init(800,600)` returns `true`, and the
bench runs:

```
simple-vulkan-2d w=800 h=600 rects=64 frames=300 readback=true ms=2396 fps~=125
  draw_us=561150 batch_us=857705 present_us=850054 readback_us=127285
```

against C's `fps=6774.8` -- **C is ~50-95x faster; Simple reaches ~1.4%**. Cost
is spread evenly across draw/submit/present, the shape of per-op interpreted
marshalling rather than GPU time. Full numbers:
`doc/10_metrics/gpu/vulkan_2d_simple_vs_c_linux_2026-09-06.md`.

Two defects found while re-measuring, filed but not fixed here: the compare gate
prints `compare_status=fail` yet **exits 0**, contradicting its own header; and
the C leg's checksum is not stable across runs (10505124 -> 6558172) while the
Simple leg's is, so cross-leg pixel parity is not yet supportable.

### Upstream

Both fixes belong upstream in `bytecodealliance/wasmtime`
(`cranelift/jit/src/{compiled_blob,memory}.rs`): the range check is a plain bug,
and the contiguous per-module code region is the same thing wasmtime already
does for its own allocator. Carried here as a local vendored patch, commented at
each edit site, until that lands.
