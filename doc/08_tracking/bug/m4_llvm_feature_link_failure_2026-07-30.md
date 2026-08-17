# Bug: `--features llvm` build — RESOLVED (was a compile-time visibility error, not a link failure)

- **Date:** 2026-07-30
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  succeeds on current origin.

> **Correction (parent session, 2026-07-30).** Two independent lanes checked
> this. The `pub(crate)` visibility on `process_c_runtime_arg_indices`
> (`codegen/instr/calls.rs:2550`) was **already on origin** before either lane
> started — `git show <origin>:…` confirms it — so no fix "landed in this
> lane"; the E0603 diagnosis was against a stale tree. The second lane made
> zero edits and both builds passed: `cargo build --release -p simple-driver
> --features llvm` and the same command without the feature, exit 0 each.
>
> **Scope caveat — two different LLVM problems, do not conflate them:**
> this doc covers the *seed's* cargo `llvm` feature build, which works. The
> long-standing "62 undefined symbols" note in `.claude/rules/bootstrap.md`
> is a *different* failure — the LLVM **stage-2 link** of the pure-Simple
> compiler, tracked in
> `seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`. M4 was previously
> described as blocked on "62 undefined LLVM symbols"; that framing was wrong.
> The seed builds with LLVM; what remains unproven for M4 is the stage-2 LLVM
> link path, and Cranelift remains the working stage-2/3 backend.

- **Original status line (superseded):** fixed — one-line visibility fix landed in this lane
- **Severity:** blocker for M4 (LLVM-backend memory instrumentation / `--mem-infra`)
  before the fix; the feature is now buildable.
- **Binary under test:** Rust seed `src/compiler_rust/target/release/simple`
  (bin from crate `simple-driver`), built by this lane with
  `cargo build --release -p simple-driver --features llvm`, exit 0. No other
  `src/**` file was modified by this lane except the one line below and this
  doc.

## 1. Exact repro command

The task's suggested repro (`-p simple`) does not resolve — there is no
package named `simple` in the workspace; `cargo build -p simple` fails
immediately with `error: cannot specify features for packages outside of
workspace` (65-byte error, not a link failure). The actual crate producing the
`simple` binary is `simple-driver` (`driver/Cargo.toml`, `[[bin]] name =
"simple"`). Corrected repro, run from `src/compiler_rust/`:

```
cargo build --release -p simple-driver --features llvm
```

`llvm` is defined in `compiler/Cargo.toml`: `llvm = ["inkwell"]`, and
`inkwell = { version = "0.5", features = ["llvm18-0"] }` (optional). System
`llvm-config` on this host is 18.1.8 (`/usr/bin/llvm-config-18`,
`/usr/lib/llvm-18/bin/llvm-config`), which matches the `llvm18-0` inkwell
feature — **no version mismatch with system LLVM was found**.

## 2. What actually happened — NOT a link failure

Before today's fix, `cargo build --release -p simple-driver --features llvm`
failed at **compile time**, in the `simple-compiler` crate, before reaching
the link step at all:

```
error[E0603]: function `process_c_runtime_arg_indices` is private
    --> compiler/src/codegen/llvm/functions/calls.rs:2482:78
     |
2482 |             } else if let Some(text_indices) = crate::codegen::instr::calls::process_c_runtime_arg_indices(sffi_name)
     |                                                                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ private function
note: the function `process_c_runtime_arg_indices` is defined here
    --> compiler/src/codegen/instr/calls.rs:2545:1

error[E0603]: function `process_c_runtime_arg_indices` is private
    --> compiler/src/codegen/llvm/functions.rs:2672:70
     |
2672 |                     let text_indices = crate::codegen::instr::calls::process_c_runtime_arg_indices(runtime_name)
     |                                                                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ private function

error: could not compile `simple-compiler` (lib) due to 2 previous errors; 2 warnings emitted
```

Only these **2** errors, both the same root cause, both in
`llvm`-feature-gated modules (`codegen/llvm/functions.rs` and
`codegen/llvm/functions/calls.rs`) calling a private free function defined in
the always-compiled `codegen/instr/calls.rs`. This is a plain Rust
visibility bug: the function has no `pub`/`pub(crate)` modifier, so it's only
visible within its own module, but two sibling modules (only reachable under
`--features llvm`) call it via `crate::codegen::instr::calls::…`. Since the
non-`llvm` default build never compiles `codegen/llvm/*`, this visibility gap
was invisible until the `llvm` feature was actually turned on — which is
presumably why it was standing.

**Census:** 2 distinct error sites (both `E0603`, both the identical private
function), 0 undefined-symbol / linker errors of any kind. The "~62 undefined
symbols" figure in the task's blocker description does not match what this
lane reproduced — either that figure was recorded against a different
tree/commit, or it was a mis-classification of a downstream stub caused by
the compile failure never actually being reached (a compile error upstream
would abort the build before generating any object files to link, so a
"linker" step could not have run at all against this crate in this state).

## 3. Root cause

`src/compiler_rust/compiler/src/codegen/instr/calls.rs:2545` declares:

```rust
fn process_c_runtime_arg_indices(func_name: &str) -> Option<(&'static [usize], &'static [usize])> {
```

with default (private-to-module) visibility. It is used:
- Locally within the same file at line 3137 (fine, same module).
- From `codegen/llvm/functions.rs:2672` and
  `codegen/llvm/functions/calls.rs:2482` via a fully-qualified
  `crate::codegen::instr::calls::…` path — both call sites live in code paths
  that only compile under `--features llvm`.

Not a missing LLVM library, not an `llvm-config --libs` delta, not an
inkwell/LLVM version mismatch — purely a Rust-visibility oversight that only
manifests when the `llvm` feature is enabled.

## 4. Fix applied (one-liner)

```rust
// src/compiler_rust/compiler/src/codegen/instr/calls.rs:2545
- fn process_c_runtime_arg_indices(func_name: &str) -> Option<(&'static [usize], &'static [usize])> {
+ pub(crate) fn process_c_runtime_arg_indices(func_name: &str) -> Option<(&'static [usize], &'static [usize])> {
```

## 5. Verification

```
$ cd src/compiler_rust && cargo build --release -p simple-driver --features llvm
   ...
    Finished `release` profile [optimized] target(s) in 2m 56s
$ echo $?
0
```

Binary produced at `src/compiler_rust/target/release/simple` and runs:

```
$ ./target/release/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```

No undefined-symbol / linker errors occurred at any point after the
visibility fix. Remaining build output is warnings only (pre-existing,
unrelated: `rt_*` extern-fn redeclaration-signature warnings in
`runtime/src/value/sffi/{memory,time}.rs`, and two `unused_assignments`
warnings in `compiler/src/interpreter/../interpreter_call/block_execution.rs`
— none introduced by this change, none feature-gated on `llvm`).

## 6. Scope note for M4 follow-up

This closes the *build* blocker only. It says nothing about whether the
LLVM-backend memory-instrumentation (asan/memprof) passes behind
`--mem-infra` are implemented, correct, or wired up at runtime — that is
separate M4 work, not attempted in this lane per the "if the fix is a
one-liner, apply and verify the build; otherwise do not attempt large
changes" instruction. The build being green removes the precondition
blocking that work from starting.
