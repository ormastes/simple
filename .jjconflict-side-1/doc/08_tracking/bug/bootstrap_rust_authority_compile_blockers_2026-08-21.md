# Bootstrap Rust authority compile blockers (2026-08-21)

## Status

Rust authority compile blockers are fixed upstream. The duplicate traversal
helper was removed and the `dispatch_profile` module was restored. A focused
`cargo check -p simple-compiler` passed before the rebase.

The next measured run reached Stage 2 and exposed a separate pure-Simple schema
defect: `_FlatAstBridge/convert_nodes.spl` constructed
`PatternKind.TypeTest`, but `parser_types_expr.spl` did not declare that enum
variant. The lane adds it last to preserve all existing ordinal values. The
same run also proved the stage-log classifier missed uppercase native-build
summaries; its case-insensitive diagnostic fixture now passes.

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

Rerun the measured Stage-2 command once, then produce a planner receipt and
continue through Stage 3/4. Do not substitute the Rust seed for normal Simple
checks and do not hand-write Stage-2 receipts.
