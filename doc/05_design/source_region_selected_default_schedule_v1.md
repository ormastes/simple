# Selected ordinary default scheduling, checkpoint1

Status: source implementation for independent review. All seven authored SSpec
controls are UNRUN. No driver activation, replay permission or general default
P1 closure is claimed. Root owns landing; the actual archive owner owns its
private entry/error/lifetime hooks and has not installed this scope yet.

Actual ordinary module emission previously used function dictionary value
order. A helper could be emitted before post-lowering SOURCE closure discovery,
so its actual default occurrences could not be retroactively retained. The
new opt-in worklist runs after normal target/provider setup and prescan, before
the existing ordinary body loop. It emits each selected root through the SAME
`lower_module_emit_fn_v1`. The actual `emit_resolved_direct_call` seam observes
the resolver-selected SymbolId and enqueues internal target bodies once,
including calls normally lowered from defaults. It changes no verification
flags, argument/default dispatch, ABI behavior or body emitter.

The queue is discovery order, not topological order. A callee discovered during
root emission runs later; completed IDs suppress only those exact bodies from
the ordinary remainder. Completion requires an eligible archive-selected,
nonextern, nongeneric body actually present in builder.module under its key,
no active builder and no new lowering errors. An excluded/skipped declaration
never becomes completed. Recursive calls terminate through queued-ID membership.
The actual ordinary input module replaces the prepared function-table view at
binding, preventing selectors from substituting a stale prepared body graph.
Name/path comparison is not archive authority: the private driver must bind
its real loaded/admitted target and current lowerer throughout this calltree.

`source_region_prepare_default_schedule_v1(source,target_key,producer,consumer,
account)` installs only idle scratch. `source_region_drain_default_schedule_v1`
is the ordinary module-owner hook. `source_region_finish_default_schedule_v1`
checks observation completeness only; it returns no receipt or public frame.
`source_region_clear_default_scope_v1` releases retained references. The actual
archive owner MUST clear on all success/abort paths before promotion and
transient scope end; that wiring is a remaining prerequisite, not an optional
caller convention for activated SOURCE.

After the actual provider artifact loader has authenticated bytes and completed
ordinary relocation, a hook records current original-function identity, use
ordinal, original artifact provenance and freshly encoded target-bound HIR.
The actual local-field fallback records its genuine owner key/ordinal and input
bytes separately, with no fabricated artifact. Resolver/default hooks require
the actual builder owner to match the selected function. Rows are observations,
not admitted repository records. No getter consumes them for SOURCE replay in
this checkpoint. A shared artifact key never collapses multiple lexical uses.

New queue scans, native typed map has/index operations, growth and codec work
are prepaid on the supplied actual shared account. There is no new dictionary
snapshot or full-module serialization. Each ordinary remainder skip scan is
paid. Absent opt-in state adds only constant condition checks, with no new scan
or allocation. The existing ordinary compiler body/default loading/relocation
runs once in its explicit compiler resource domain, not behind a fake SOURCE
budget. New observation/encoding work does use the SOURCE request account.

A failure latches one fixed error reference, stops further observations and
queue/remainder work, and returns from lower_module before subsequent thunk or
metadata publication. The current ordinary body may finish only in the ordinary
compiler domain. A fixed diagnostic/error-vector allowance is reserved at
preparation; an existing ordinary error is preserved instead of duplicated.
The actual archive Err route must discard partial compiler output. There is no
new activation or success claim from partial output or a failed worklist.

Tests use real frontend and ordinary MirLowering: actual earlier inventory
helper plus recursion emitted once with ordinary MIR equality; a real omitted
field and its default-subtree callee; stale prepared graph cannot replace the
actual ordinary body; one-short preparation; exhaustion stopping remainder and
one diagnostic; extern/filter refusal never completing a skipped body. No fake
MirFunction, default capture or admission receipt is used.

Required next boundaries: actual referenced target-symbol/type/layout closure
snapshots, unchanged binding validation allowing unrelated plan additions,
same original-function lexical namespace on replay, exact occurrence cursor
consumption, transitive parameter defaults and global alias/initializer
dependencies, driver lifetime/reset wiring, and actual end-to-end positive.
Unknown or missing proof is a prerequisite, not a permanent removal of valid
omitted defaults. Logical accounting here does not qualify native physical
capacity, allocator behavior, runtime performance or whole compiler bounds.
