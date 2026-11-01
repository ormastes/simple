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
- [ ] Land the receipt save fix, commit 8ba03f0c10c on local branch
  work/native-codegen-fixed-cost; not compiled or reviewed. About 95% of a 20s
  worker sample was in the O(n^2) `reverse_reference_sorted_v1`, and real
  codegen is about 1s per module, so shards may not be needed after it.
- [ ] Per-batch cache scope dirs can be evicted before the final link
  (`disk_bound_keep_newest_dirs`, keep 6, 6h). Set
  `SIMPLE_NATIVE_CACHE_SCOPES_KEEP` or fix; code-read inference, not observed.
- [ ] Receipts under `build_cache.sdn.reverse-references/sha256/` are never evicted.

## Erased generics coverage gaps

- [ ] Arithmetic where both operands are erased computes on tagged words.
- [ ] `@always_inline` bodies forwarding `T` to an i64 extern decode wrongly if
  the emitted body is called instead of inlined.
- [ ] No adapter thunks: a concrete `fn(..) -> i64` passed into `fn(.., T) -> T`
  has a raw ABI, wrong for scalars.

- [ ] `T`-typed struct fields are stored raw by instance, but a read inside an
  erased body has HIR type `T` and decodes as tagged. User enum `T` payloads
  are the same class.

## Specs and gates

- [ ] Rework the stale `generic_return_owner` spec.
- [ ] `trait_typed_receiver_dispatch_spec`: devirtualization counts are 0.
- [ ] Lease script kinds.
- [ ] `check-guard-wiring.shs` fails on this branch and needs triage.
