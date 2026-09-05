# Pure-Simple full CLI bootstrap recovery — local research

Date: 2026-07-17

## Scope

Recover the pure-Simple Stage 2/3/full-CLI path without using a Rust seed as
normal tooling and without racing other worktrees or deleting useful caches.
Research was performed against clean `origin/main` revision `f6e7e2a18e5`.

## Parallel findings

### LLVM Stage 2 source failures

Seven remaining `llvm global load referenced undeclared symbol` failures were
source or frontend-shape defects, not an LLVM fail-open problem:

- CUDA used bare enum value `CompareExchange` outside pattern context.
- HIP and OpenCL used soft keyword `shared` as a local and parameter.
- `SliceIter<T> { ... }` entered unsupported generic brace-literal recovery.
- `Iterator.collect<C>` depended on method generics that HIR currently drops.
- `Array.allocate` was not a dynamic-array API.
- `Tensor<T, N>.ndim` used type parameter `N` as a runtime value.

LLVM correctly rejected the resulting undeclared globals. The source fixes
remove those invalid shapes; generic `Iterator.collect` restoration remains a
tracked compiler feature in
`doc/08_tracking/bug/iterator_collect_generic_restoration_2026-07-17.md`.

### SimpleOS strict native crash

Stage 218/220/223 crashed in `Map.values` after MIR lowering continued past an
explicit `return`. A second path treated qualified `Dict.values` as an ordinary
method instead of the builtin runtime operation. The root fixes are:

- stop lowering a block after its builder has an explicit terminator;
- allow qualified `Dict`/`dict` builtin dispatch.

Stage 229 was diagnostic Rust-seed output with 13 unresolved stubs and is not an
admitted runner.

### Native object loss

Stage 2/3 previously lost a system temporary directory during object emission.
The first recovery prototype retained all fresh object bytes and retried, but
that increased memory pressure. The selected design preserves the existing
file flow and stages objects in a unique directory beside the configured cache.
It is outside both system-temp cleanup and the cache subtree removed by
`--clean`.

## Host evidence boundary

The existing memory-lane Stage 2 and Stage 3 binaries passed their build logs,
but its full CLI was still compiling with no admitted output during research.
This host also had load above the heavy-work threshold and essentially full
swap. No duplicate bootstrap was started. Final full-CLI, font acceptance,
SimpleOS pixel, native GPU, and performance claims remain evidence-gated.
