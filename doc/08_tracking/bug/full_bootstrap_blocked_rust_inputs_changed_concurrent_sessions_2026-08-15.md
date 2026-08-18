# Full bootstrap blocked: Rust inputs changed mid-build (concurrent sessions)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

Date: 2026-08-15. Session: sole temporary build owner attempting to replace the
seed-masquerading `bin/simple` with a self-hosted binary.

## State before
- `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` (59,356,648 B,
  mtime 2026-08-15 00:50) printed the Rust-seed WARNING banner — a seed copy at
  the self-hosted path (the exact anti-pattern bootstrap.md warns about).
- No Rust seed existed at `src/compiler_rust/target/bootstrap/simple`.
- Native cache effectively cold (6 `.o`).

## Attempts and exact errors
1. `bin/simple build bootstrap` (seed): Stage 1 FAILED —
   `error: native-build worker timed out after 180s before producing a binary.`
2. `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`:
   `bootstrap-policy-error: reason-receipt-required` (exit 64). Fixed by a
   canonical receipt (`reason=seed-missing`, target `//bootstrap:stage4`).
3. Silent exit 1: the wrapper computes `repo_root` with logical `pwd` while
   `bootstrap-stage3-provenance.shs` uses `pwd -P`; invoking through the
   symlink `/home/ormastes/dev/pub/simple -> /mnt/data/worktrees/simple-main`
   makes the facade's self-path check `return 1` with no message. Workaround:
   invoke with physical cwd/PWD. (Wrapper bug worth its own fix: fail loudly.)
4. `--full-bootstrap --deploy` from physical path: cargo seed build ran
   (~30 min), then:
   `error: Rust inputs changed during full bootstrap; refusing to publish a stale seed`
   (wrapper exit 1). Root cause: other agent sessions are concurrently editing
   `src/compiler_rust/**` in this shared working tree (git status shows ~15
   modified Rust files, changing during the run). The guard is correct; the
   environment cannot currently satisfy it.

## Stage reached
Stage 0 (Rust seed build) completed compiling but was refused publication; no
Stage 1/2/3/4 was reached. `bin/simple` remains the seed
(sha256 06548f16a4455743e45f1fb117f0110ab77511ac2b6926f4b2fb9d34cb78a477,
59,369,576 B, mtime 2026-08-15 01:03 — note: replaced by another session
mid-run; still prints the seed banner).

## Unblock conditions
- Quiesce concurrent `src/compiler_rust/**` edits (single-writer window), or
- run the full bootstrap from a snapshot/worktree pinned to a commit, then
  deploy the resulting binary back.

Logs: rust-seed-build logs under
`build/bootstrap/logs/x86_64-unknown-linux-gnu/`; session logs in scratchpad
`boot4.log`/`boot5.log`.

## Status re-check 2026-08-17 — STILL BLOCKED, precondition re-measured

binary identity: `readlink -f bin/simple` = `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`; `stat -c '%s %y'` = `59537240 2026-08-17 12:58:51.339525019 +0000`

The blocking precondition (concurrently-edited Rust inputs in this shared
working tree) is still true today — the guard would fire again on any
`--full-bootstrap`:

```
$ git status --porcelain src/compiler_rust src/runtime
 M src/compiler_rust/compiler/src/codegen/instr/core.rs
 M src/compiler_rust/compiler/src/hir/lower/expr/operators.rs
 M src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs
 M src/compiler_rust/compiler/src/interpreter/expr/calls.rs
 M src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs
 M src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs
 M src/compiler_rust/compiler/src/interpreter_extern/system.rs
 M src/compiler_rust/parser/src/lexer/strings.rs
 M src/compiler_rust/runtime/src/value/core.rs
 M src/compiler_rust/runtime/src/value/sffi/env_process.rs
 M src/runtime/runtime_process.c
?? src/compiler_rust/target_wt/
?? src/runtime/runtime_terminal_mode_impl.h
?? src/runtime/runtime_terminal_signal_scope_impl.h
```

Note the dirty set is DIFFERENT from the one frozen on 2026-08-15 (11 tracked
files vs 17, only a partial overlap), which is itself the evidence that the tree
is still being edited concurrently. No full bootstrap was attempted — running one
was explicitly out of scope for this session, and doing so under these conditions
would reproduce `Rust inputs changed during full bootstrap` rather than teach
anything new. The guard is correct; the environment still cannot satisfy it.
Requires a quiesced tree or a private worktree with a frozen `src/compiler_rust`.
Nothing changed.
