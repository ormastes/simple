# Erased generics and bootstrap follow-ups (2026-11-01)

State at close: stage3 from the erased generics branch passed HIR and MIR with
0 E-GEN-001 and is in sequential codegen. Its link, hello check and later
phases are not verified.

## Bootstrap

- [ ] Stage3 full link, then build and run hello with the result. Confirm every
  closure module reaches codegen; an earlier probe on the pre-fix stage2 reached
  codegen with 8 of 1537 modules, unexplained.
- [ ] Rebuild stage3 with itself, file by file (`SIMPLE_FILE_WORKERS=1`, no green
  run on record), with per-layer archives linked into the binary.
- [ ] Stage4 from `src/app/cli/main.spl`, then the full test suite on it.

## Codegen speed

- [ ] Parallel native codegen shards; see
  `doc/03_plan/compiler/native_codegen/step5_real_parallelism_plan_2026-09-04.md`.
  Sequential codegen measured about 39s per module, about 15 hours in total.
- [ ] Replace the O(n^2) `reverse_reference_sorted_v1` in
  `src/compiler/80.driver/cache/reverse_reference_receipt.spl`. A 20s sample of
  the worker had 51% of samples there, and cost does not track module size.

## Erased generics coverage gaps

- [ ] Arithmetic where both operands are erased computes on tagged words.
- [ ] `@always_inline` bodies forwarding `T` to an i64 extern decode wrongly if
  the emitted body is called instead of inlined.
- [ ] No adapter thunks: a concrete `fn(..) -> i64` passed into `fn(.., T) -> T`
  has a raw ABI, wrong for scalars.

## Specs and gates

- [ ] Rework the stale `generic_return_owner` spec.
- [ ] `trait_typed_receiver_dispatch_spec`: devirtualization counts are 0.
- [ ] Lease script kinds.
- [ ] `check-guard-wiring.shs` fails on this branch and needs triage.
