# `bin/simple` aborts intermittently: AArch64 JIT branch relocation out of ±128 MB range

**Filed:** 2026-09-05
**Severity:** medium — non-deterministic abort of any JIT-executed tool invocation on aarch64
**Status:** open, **now reproduced deterministically** (2026-09-06, see below)
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
With that in place `is_pic` can be true on aarch64 and every call goes
indirect, making the ±128 MB displacement irrelevant.

**Not done here** because `vendor/cranelift-jit/**` is vendored third-party code
and CLAUDE.md scopes it out; this needs an explicit decision to patch vendor (or
to carry the change upstream). Filed with the reproducer so that decision can be
made on evidence.
