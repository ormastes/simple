# Seed JIT: unresolved symbols SIGSEGV or silently pass instead of diagnosing

**Status:** OPEN — seed-owned; the fix must land in `src/compiler_rust` (out of
scope for pure-Simple sessions per "Fix .spl not Rust"). Fence lands RED on the
roster so the gap stays visible.
**Found:** 2026-08-10, seed at `f74a76ae240` (`bin/release/x86_64-unknown-linux-gnu/simple`, Rust seed).
**Fence:** `scripts/check/check-jit-unresolved-symbol-guard.shs` (roster:
`check-aot-lane-fences.shs`). Fixtures: `test/fixtures/jit_unresolved_symbol_guard/`.

## Symptom

Bad input that the interpreter rejects with a clean semantic error either
hard-crashes or silently succeeds on the default JIT lane (`bin/simple file.spl`).

| input | interpreter (`SIMPLE_EXECUTION_MODE=interpreter`) | JIT (default) |
|---|---|---|
| `var x: [i64] = []` (control) | OK | OK |
| `var x = [i64]()` — list literal `[i64]` CALLED | `error: semantic: variable 'i64' not found`, rc=1 | **SIGSEGV rc=139** |
| `var x = [i64](5)` | same diagnostic | **SIGSEGV rc=139** |
| `var y = undefined_var_xyz` (bare read) | `variable 'undefined_var_xyz' not found`, rc=1 | **prints OK, rc=0 — FAILS OPEN** |
| `undefined_fn_xyz()` | diagnostic | diagnostic rc=1 (OK) |
| `UndefinedType()` | diagnostic | diagnostic rc=1 (OK) |
| `s.undefined_method_xyz()` | diagnostic | rc=70 "unresolved symbol" runtime refusal (loud, acceptable) |

`[T]()` is deliberately NOT a typed-empty-array constructor (deferred language
question — would need seed + pure-Simple parser + MIR lowering in lockstep).
The correct behavior for all rows is the interpreter's diagnostic.

## Root cause (seed)

Backtrace of the SIGSEGV (gdb, thread `simple-main`):

```
#0  0x000002c2cc5b14a5 in ?? ()                       <- JITted code region
#4  simple_compiler::codegen::jit::JitCompiler::call_i64_void
#5  <...LocalExecutionManager as ExecutionManager>::execute
#6  simple_driver::exec_core::ExecCore::run_file_jit
```

Two missing guards in the seed JIT lane, both absent from its own interpreter
lane (drifted duplicate of the same semantic check):

1. **Undefined variable reads fail open.** The JIT lane materializes an
   unresolved variable as a garbage/default value instead of raising
   `variable not found` (proven by the `undef_var` row: rc=0, body executes).
2. **Indirect call does not validate the callee.** `[i64]()` becomes a list
   value built from that garbage; the call lowering loads a "function pointer"
   from a non-callable value and jumps to it (`call_i64_void` → frame #0 in
   unmapped JIT memory) → SIGSEGV.

## Lane ownership (positively established)

- Crash frames are Rust seed symbols (`src/compiler_rust/compiler/src/codegen/jit.rs`).
- The pure-Simple compiler is NOT on this path and is CORRECT: `bin/simple
  native-build --entry repro.spl` fails cleanly with
  `error: HIR lowering error in repro.spl: unresolved name: i64` (verified 2026-08-10).
- Interpreter lane (also seed Rust) is correct.
- Stage-3 self-hosted binary has no file-run subcommand, so it cannot host this
  lane at all.

## Why nothing caught this

`bin/simple test` hard-defaults to the tree-walk interpreter; no `*_spec.spl`
can observe the JIT execution lane (same structural gap documented in
`check-aot-lane-fences.shs`). There is also no bad-input/crash corpus for the
JIT lane. The fence above is the coverage fix: it drives the real JIT lane and
fails closed (crash = FAIL, silent green = FAIL, rc-without-diagnostic = FAIL).

Sabotage proof (2026-08-10): real binary → FAIL naming exactly
`typed_ctor/jit CRASH rc=139` and `undef_var/jit SILENT PASS`; wrapper forcing
interpreter on both lanes → PASS; fail-open stub printing OK/rc=0 → FAIL on
all four bad-input lane-cases.

## Fix direction (for a seed-authorized session)

Share, don't re-duplicate: hoist the interpreter's unresolved-variable semantic
check to run before/within JIT lowering (one shared resolver verdict for both
lanes), and make the JIT's indirect-call lowering refuse non-callable callee
values with a diagnostic instead of jumping.
