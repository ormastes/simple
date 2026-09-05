# HIR destination graph registry handoff

## Ownership

`hir_destination_registry.spl` is the sole process owner of every
`HirDestinationGraph`. One slot represents one complete compilation and owns
all module rows in that compilation. Callers carry only `(slot, generation)`
scalars. The current no-GC Stage3 route is deliberately process-lifetime and
process-serialized: acquire succeeds exactly once, constructs one lazy slot,
and one `HirLowering` owner performs every write.
Scalar leases are copyable and are not locks; parallel callers must add
synchronization outside this registry before sharing the facility.

The only lifecycle is BUILDING -> READ -> CONSUMED, or BUILDING -> FAILED.
Release and abandon change only terminal state: they do not clear, recycle,
free, replace, or reassign the graph. All arena storage remains rooted until
process exit. A second compile/acquire fails closed, so READ slot count is
bounded exactly to one.

Abandon copies the exact slot/generation scalars into
`HirLowering.failed_destination_slot` and `failed_destination_generation`
before clearing the active lease. That failed receipt authorizes only
`hdr_diagnostic`, `hdr_error`, and the three accounting readers. Every semantic
row reader remains READ-only. CONSUMED authorizes no diagnostic, accounting, or
semantic data read; only the lifecycle state query can observe the terminal.

The scalar `structural_capacity_bytes_estimate` is a conservative schema-based
capacity estimate, not allocator usage or RSS. `owned_text_payload_bytes` is
the exact byte length of text reachable from every initialized backing slot,
including rollback-retained suffixes, plus its high-water scalar. Freeze
computes it in O(total initialized capacity). Process RSS and real allocator
high-water remain measurement obligations.

## Integration surface

- `HirLowering.enable_destination_graph(generation)` opts into graph mode.
- `freeze_destination_compile`, `release_destination_compile`, and
  `abandon_destination_compile` preserve scalar lease ownership; compatibility
  graph-named methods forward to these compile-lifetime methods.
- Module reservation/failure/finalization is scalar, and function reservation
  requires its owning `module_index`.
- Token-to-function and per-module reservation indexes make module publication
  and compile freeze O(N + modules + functions), where N includes initialized
  arena capacity slots (including rollback-retained suffixes) and range edges.
  Total graph construction/freeze remains O(N + M + F), subject to
  runtime measurement; duplicate or missing membership is rejected without a
  quadratic function scan.
- `hir_destination_registry_writer.spl` exports the complete fixed writer,
  reservation/range/checkpoint/function facade.
- `hir_destination_registry_reader.spl` exports frozen guarded scalar readers.
- `hir_lowering/__init__.spl` is the package umbrella.

Flat mode retains `destination_slot=-1`, `destination_generation=-1`, and
`destination_mode=HD_MODE_FLAT`; it does not call acquire and therefore does not
allocate a graph.

## Static review evidence

- Every fixed `write_*`, reservation, module/function finalization, checkpoint, and
  rollback method in the destination schema has a scalar registry wrapper.
- Every existing scalar `*_at`/float/block/function reader has a frozen wrapper;
  aligned range-length and row-count readers fill the schema traversal gaps.
- Search found no graph argument, graph return, graph getter, local binding from
  `_hir_destination_graphs[slot]`, or assignment of a populated graph.
- All registry/facade files are below 800 lines; `git diff --check` passed.

No compiler, build, test, benchmark, optimizer, or SPipe command was run, per
the source-only handoff constraint. Runtime correctness remains unverified.
