# origin/main unbuildable: E0308 CowEnv at interpreter_eval.rs:1777 (2026-08-25)

## Symptom

`cargo check --release --bin simple` fails on pristine `origin/main`
(`d813ea19dd9`) in a clean `git worktree add --detach` checkout:

```
error[E0308]: mismatched types
  --> compiler/src/interpreter/../interpreter_eval.rs:1777:29
   |  if bind_module_namespace_after_import(
   |      env,   expected `&mut CowEnv`, found `CowEnv`
```

Same incident class as
`origin_main_unbuildable_rust_seed_2026-08-11.md` and
`origin_main_unbuildable_missing_half_1e40de916bb_2026-08-18.md`: an
incomplete change landed (call site not updated when
`bind_module_namespace_after_import` gained/kept a `&mut Env` first
parameter), and pushes over it kept passing.

Found while verifying an unrelated one-line `interpreter_call/bdd.rs` change:
the first clean-worktree `cargo build` failed with this pre-existing error
(confirmed pre-existing by reverting the local edit and re-checking — still
2 errors). The shared worktree additionally showed 8 different errors from
other in-flight sessions; per the gate-FAIL-needs-clean-worktree rule those
were ignored and only the clean-checkout error was acted on.

## Fix

One line: pass `&mut env` at the call site (interpreter_eval.rs:1777).
Landed together with the `planned` BDD marker commit; verified by a full
`cargo build --release --bin simple` in the clean worktree.

## Guard status

`check-seed-builds-push.shs` (content-keyed, fail-closed since 2026-08-18)
would have caught this — the pushing lane evidently did not run it (hook
bypass, same failure mode as the 2026-08-11 incident). No new guard needed;
the existing guard's marker store simply has no green entry for this content,
so the next guarded push would have FAILed.
