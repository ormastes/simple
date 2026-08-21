# Bootstrap Rust authority compile blockers (2026-08-21)

## Status

Open. This blocks creation of the measured pure-Simple Stage-2 trust root and
therefore blocks the Stage 1-4 bootstrap evidence required by the lightweight
push gate.

## Reproducer

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
```

The bootstrap-only Rust authority exits 101 before Stage 2 with:

- duplicate `eval_dict_for_each` definitions in
  `compiler/src/interpreter_helpers/collections.rs`;
- unresolved `crate::interpreter::dispatch_profile` from
  `compiler/src/interpreter/expr.rs`;
- unresolved `crate::interpreter::exec_block_closure_into` from the collections
  helper.

Evidence is retained at
`build/bootstrap/logs/x86_64-unknown-linux-gnu/rust-seed-build.log` in the
isolated verification worktree.

## Unblock condition

Land the independently owned Rust interpreter fixes on `origin/main`, then run
the measured Stage-2 command once. Do not substitute the Rust seed for normal
Simple checks and do not hand-write Stage-2 receipts.
