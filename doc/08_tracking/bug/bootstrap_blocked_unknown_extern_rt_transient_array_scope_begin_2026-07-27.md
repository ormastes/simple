# Bootstrap is blocked repo-wide: stage 1 dies on unknown extern rt_transient_array_scope_begin

- **Filed:** 2026-07-27
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** blocks ALL compiler-side work — no fix to `src/compiler/**` can be
  verified until this is cleared, because the only way to exercise such a fix is
  to rebuild the compiler.

## Symptom

```
=== Stage 1: Compile with seed compiler ===
error: semantic: unknown extern function: rt_transient_array_scope_begin
[STDERR] error: native-build worker exited with code 1.
  interpreter: /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple (exit code 1)
  Compile failed (exit Some(1))
Stage 1 FAILED
```

Reproduced twice, in a worktree with its own real `build/` and `bin/release`:

1. `bin/simple build bootstrap` — fails as above.
2. `build/tmp/claude_simple build bootstrap` (Rust seed as the driver) — fails
   **identically**, because `build bootstrap` still shells out to
   `bin/release/<triple>/simple native-build ...` for the actual compile. Driving
   the wrapper with the seed does not change which binary compiles.

## Cause: extern-add chicken-and-egg

- `rt_transient_array_scope_begin` is referenced from
  `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`.
- It is defined in the runtime (`src/runtime/runtime.h`,
  `src/runtime/runtime_native.c`) and known to the Rust compiler
  (`src/compiler_rust/compiler/src/elf_utils.rs`).
- It landed in `1282f6e04d7 perf(bootstrap): bound parser memory for full CL`.
- The **deployed** `bin/release/<triple>/simple` predates that commit, so its
  extern table has no entry for the symbol and it rejects the current compiler
  source.

To rebuild the compiler you must compile source that uses the new extern, but
the binary doing the compiling is the one that does not know it. This is the
documented "extern additions need a bootstrap rebuild" hazard
(`.claude/memory/feedback_extern_bootstrap_rebuild.md`) in its deadlocked form:
the rebuild that would teach the binary about the extern is itself blocked by
the extern.

## Impact

Two independent goal-blocking fixes are stuck behind this:

1. **Method-dispatch misroute** (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`)
   — a struct that merely *defines* a method name hijacks that call for a
   primitive receiver, because `struct_value_syms.get()` on the native lane
   answers an ABSENT key with another entry's value. Proven minimal: interpreter
   prints `65`, native lane prints `11` for
   `"A5".char_code_at(0).to_i32()` with two structs defining `to_i32`. Blocks the
   three host-WM showcase cells. Fix is written but **cannot be verified**.
2. **`panic` not known to HIR lowering** (`Unknown variable: panic while lowering
   FailSafeResult.unwrap`) — the current head of the web-render JIT-blocker
   chain. Compiler-side; must not be worked around in the library, since `unwrap`
   on `Err` has to abort.

## CORRECTION (2026-07-27): it is a stale-artifact problem, not a source defect

The original diagnosis below said the deployed pure-Simple binary was at fault
and that the Rust seed "already carries the symbol". **The second half is wrong**,
and the first half is incomplete. Both available compiler binaries are stale
builds that predate the symbol's registration:

```
grep rt_transient_array_scope_begin src/compiler_rust/common/src/runtime_symbols.rs
  :130   "rt_transient_array_scope_begin",          <- registered in CURRENT source
grep ... src/compiler_rust/compiler/src/interpreter_extern/mod.rs
  :283   "rt_transient_array_scope_begin",          <- wired to memory::rt_transient_array_scope_begin

strings build/tmp/claude_simple                  | grep -c rt_transient_array_scope_begin  ->  0
strings bin/release/x86_64-unknown-linux-gnu/simple | grep -c rt_transient_array_scope_begin ->  0
```

The current Rust source registers the extern; neither binary contains the string
at all. `build/tmp/claude_simple` has an mtime NEWER than the extern commit
(2026-07-26 01:52 vs 2026-07-25 14:24), which is what misled me — that mtime is
when the binary was copied, not when it was built.

Running stage 1 with the seed directly therefore fails **identically**, and the
failure names the seed itself as the interpreter:

```
error: semantic: unknown extern function: rt_transient_array_scope_begin
[STDERR]   interpreter: /home/ormastes/dev/pub/simple/build/tmp/claude_simple (exit code 1)
```

**Actual fix: rebuild the Rust seed from current source**, then drive stage 1
with the rebuilt binary:

```
cd src/compiler_rust
CARGO_TARGET_DIR=<private-dir> cargo build --release -p simple-compiler
```

Use a private `CARGO_TARGET_DIR` so the shared `src/compiler_rust/target/` is not
clobbered while other sessions are building.

No `.spl` or Rust source change is required — the source is already correct.

## Candidate resolutions (original, resolution 1 REFUTED — see correction above)

1. ~~**Compile stage 1 with the Rust seed directly**, bypassing the wrapper's
   hardcoded driver. The seed's extern table is in Rust and already carries the
   symbol.~~ **REFUTED:** the prebuilt seed predates the registration and rejects
   the symbol exactly as the deployed binary does. Correct only once the seed is
   rebuilt.
2. **Teach `build bootstrap` to accept a driver override** (an env knob for the
   native-build binary). No such knob exists today — searched
   `src/app/build/**` for `SIMPLE_*INTERP*`/`*SEED*`/`*BOOTSTRAP*` and found none.
3. **Redeploy a binary built from a revision that predates the extern**, then
   walk forward. Only works if an intermediate revision both knows the extern and
   compiles under the currently deployed binary.

Option 1 is the one to try first, and it is a repo-tooling fix, not a source
change.

## Note for whoever picks this up

Do not "fix" this by deleting the extern reference from `module_assembly.spl` —
it is load-bearing for the parser memory bound that `1282f6e04d7` added, and
removing it would reintroduce the memory blowup that commit was fixing.
