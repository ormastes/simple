# `bin/simple` aborts intermittently: AArch64 JIT branch relocation out of ±128 MB range

**Filed:** 2026-09-05
**Severity:** medium — non-deterministic abort of any JIT-executed tool invocation on aarch64
**Status:** open, observed once, not reproduced on demand
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
