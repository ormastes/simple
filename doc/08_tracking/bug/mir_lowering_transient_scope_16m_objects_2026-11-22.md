# Stage 3 MIR lowering: one per-module transient scope tracks >16M objects (`ast_semantic_value`) (2026-11-22)

Bug id: `mir_lowering_transient_scope_16m_objects_2026-11-22`
Status: OPEN — root cause inside one module's lowering not yet located; fix is a redesign (see "Why no code fix landed").
Related: `stage3_transient_scope_object_cap_panic_2026-11-20.md` (the 2^24 cap that this scope hit, now a warning),
`stage3_c_runtime_worker_memory_2x_2026-11-20.md` (~0.4 GB of tracking-list overhead from this scope).

## Symptom

Stage 3 (core-C runtime, `src/runtime/runtime_native.c`) self-build, source `1f332b24464`:

```
[transient-scope] WARNING scope 42578 tracks more than 16777216 objects; continuing (no count limit, Rust-twin parity)   # s3s3i22c, 14 shards
[transient-scope] WARNING scope 39367 tracks more than 16777216 objects; continuing (no count limit, Rust-twin parity)   # s3s3i22d, 40 shards
```

Logs: `boot-fable-lane-scripts/diaglink/s3i2/s3s3i22c.build.log.saved:12040`,
`.../w-s3s3i22d/build.log:11998`. There is exactly one warning per run.

The warning is printed by `rt_core_track_transient_immortal` when the thread's
tracking list reaches 2^24+1 entries. `rt_transient_array_scope_begin` refuses
to open a scope while that list is non-empty, so the list belongs to exactly
one scope. The count is **allocations made inside that one scope**, not the
number of live objects.

## Which scope: MIR lowering of `compiler.frontend.generated.ast_semantic_value`

Attribution comes from the log, not from inference:

- `[mir-shard] shards=40 parallel=1`: shard workers run one after another, so
  the worker-0 block (lines 11982-12039 of the i22d log) is not interleaved with
  any other process. The block ends with
  `[mir-shard] done owner=0/40@0 claimed=41 passed=41`.
- Inside that block, the per-module lowering loop
  (`driver_pipeline_lowering.spl`, direct lane) prints `[mir-slow]` after each
  module that takes >= 2 s. The warning comes after 7 such lines
  (`switch_operators_calls`, `expr_dispatch`, `method_calls_literals`,
  `hir_codec`, `mir_lowering_stmts`, `module_lowering`,
  `driver_aot_native_output`) and immediately before
  `[mir-slow] dt_ms=15463 module=compiler.frontend.generated.ast_semantic_value`.
  stderr is unbuffered, and `[mir-slow]` goes through `rt_println_str`, which
  calls `fflush(stdout)` after every line (`runtime_native.c`). So the warning
  was emitted after the 7th module finished and before the 8th finished.
- Between the `[mir-slow]` print and the next module's
  `lower_module_transient_scoped` call, the per-module loop opens no other
  transient scope. It only records go-to-end failures, stores
  `ctx.mir_modules[...]`, and reports progress.
- No flush, borrow, verify, or codegen output appears between those two lines.
  This worker had no staged codegen batch: `aop_weave` and `[NATIVE] codegen`
  for all 41 modules follow only after every module is lowered.
- The 14-shard run (i22c) shows the same position. The 2026-11-20 panic run
  died at the same point: `claimed=8 ... ICE[mir_lower] module
  compiler.frontend.generated.ast_semantic_value`, at both 14 and 28 shards.
  That ICE attribution was correct. `ice_boundary_module_start`
  (`driver_ice_boundary.spl`) writes a `start` crumb before lowering, and
  `ice_boundary_module_done` closes it after lowering. A death is attributed to
  the crumb that is still OPEN, so `ast_semantic_value` was still being
  lowered when the process died. The 2026-11-20 doc says it is "the module that
  last closed" a crumb, which is the reverse. Its alternative explanation (the
  borrow-check scope in the first staged flush) runs after the crumb is
  closed, and the i22d log has no flush at that point.

So the scope is `MirLowering.lower_module_transient_scoped`
(`src/compiler/50.mir/_MirLowering/module_lowering.spl`). It is **already one
scope per module.** The pathology is inside a single module's lowering.

Note that the largest module in the batch, `switch_operators_calls` (660 KB),
did **not** cross the threshold. `ast_semantic_value` is 256 KB and 4093 lines,
with 68 functions. The largest of those are the four ~600-line / ~250-line
`ast_semantic_encode_{expr,expr_kind,stmt,stmt_kind}` matches over the
`Expr`/`ExprKind`/`Stmt`/`StmtKind` enums, which are imported from
`compiler.frontend.parser_types_expr`. Source size is not the driver.

## Provider-feed dependence (measured vs. full build)

- On the 2026-11-20 77-module fixture closure (entry imports
  `ast_semantic_value`), gdb measured the largest MIR-lowering scope at
  **3,170,897** tracked objects.
- In the full self-build, where the provider feed (`ctx.mir_feed_modules`) is
  the whole 1607-module closure, the same module crosses **16,777,216**.

That is a >5x growth for the same consumer module. Caveat: the fixture ran
integ22 source with `--backend cranelift`, and the full build ran `1f332b24464`.
The comparison therefore mixes feed size with source revision, and the feed is
not proven to be the only variable. It points at per-consumer provider work inside `lower_module`, not at
lowering the module's own bodies. For example:

- `lower_module`'s prologue rebuilds `trait_impl_owners`,
  `global_symbol_ids`, `imported_global_initializers`, and similar tables from
  the whole provider list for every consumer;
- provider method/layout demand materialization
  (`provider_method_materialized`, `provider_layout_demand_*`) is triggered
  by a consumer of huge imported enums.

This is a hypothesis to measure, not a finding.

## Why no code fix landed

The task asked to narrow the scope, for example to one scope per function
inside the module. That is a redesign here, not a mechanical narrowing:

1. Everything `lower_module` writes into the shared `MirLowering` during a
   function is enumerated as the module escape set: `errors`,
   `composite_layout_*`, `struct_field_*`, `builder`, provider-type relocation
   journals, reverse-reference batches, and the ambient-bootstrap
   `_bootstrap_mir_*` / `_bootstrap_fn_*` registries (see
   `lower_module_transient_scoped` and `transient_owner.spl`). A per-function
   scope would have to promote that whole inventory at every function
   boundary. That is O(functions x inventory) and risks a perf regression on
   every module to fix one.
2. If the growth really is per-consumer provider work (above), it happens in
   the module prologue and in cross-function demand caches. A per-function
   scope would not reclaim it, because those tables must outlive each
   function.
3. Nobody has measured which part of the module's lowering makes the
   allocations. The Rust-runtime Stage 2 (integ25) has no tracking list and no
   warning, so it cannot count them. Only the core-C Stage 3 binary can, and
   only with gdb on the TLS `rt_core_transient_heap_scope_object_len`, as in
   the 2026-11-20 doc.

## Next steps (concrete)

1. **Measure, per section.** Under a core-C Stage 3 binary, lower
   `ast_semantic_value` once with a 77-module feed and once with the full
   1607-module feed. Read `rt_core_transient_heap_scope_object_len` at the
   existing `mir_section_profile_mark` points (`s1_lowered`, ...) and at
   prologue end. Run it with gdb or with a one-shot env-gated `eprint` of
   `rt_transient_array_scope_identity_v1` plus the count. The first section
   whose count grows with the feed is the target.
2. **If the prologue / provider tables dominate:** hoist the per-consumer
   rebuild out of the module scope. Build it once per feed, in a session
   scope or as a promoted cache keyed by the feed. Or make it demand-driven
   against the consumer's actual imports. This is the same move the MIR setup
   phases (struct prescan, enum and composite inventory) already make in
   `driver_pipeline_lowering.spl`: "one transient scope per setup PHASE, not per module".
3. **If function bodies dominate:** look for O(n^2) immutable-array growth
   (`x = x.push(...)` inside the big match lowering), which allocates one new
   array object per arm.

## Cost while open

- 12 bytes per tracked entry (pointer plus `uint32_t` scope id): about 0.2 GB
  at 2^24 entries, and about 0.4 GB with doubling slack.
- All of the module's lowering scratch is held until the scope ends.
- Not fatal since PR #10530.
