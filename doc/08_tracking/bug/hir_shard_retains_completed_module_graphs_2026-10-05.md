# HIR cache shard retains completed module graphs

Status: source repair draft; native lifetime and RSS qualification UNRUN.

## Observed terminal evidence

`runtime/windows-restart-20261004/p3-next1986499-cranelift80-max` used
producer27ac (source407be) and target1986499. Its collector log SHA256 is
`9dc7a9321984590b0e792fd67b4ca695e797faf7ff940b71afa3afb9f54bdf56`.
The authenticated Job receipt records RSS-cap exit88, peak6,841,916KiB against
6,835,937KiB, quiescent1 and zero abnormal NTSTATUS. This is resource failure,
not an observed access violation. HIR progress was still active; interleaved
progress counters are not an authoritative final completed-module census.

The log does not measure individual object retention or per-process memory.
It therefore cannot establish how much of the RSS this repair will recover.

## Source mechanism

The parent starts its HIR prepass before starting the final native worker;
concurrent parent/final-worker full-HIR retention is not supported by that route.
Inside the streaming HIR shard, every cold HirModule was promoted out of its
transient scope and retained in module/validation dictionaries. Cache hits also
decoded persistent graphs. Yet shard completion exits before the later passes
that consume those graphs. Core-C promoted heap values are immortal in this
lane; deleting dictionary insertions alone does not reclaim their allocations.

## Transaction ownership

The dedicated shard path begins one scope before cache load or parse/lower.
It writes full HIR with the existing atomic `hir_cache_store_in_owned_scope`
codec owner, without nesting a scope. It retains no module body after the
transaction. Successful cache storage is required before PASS publication.

Roots that survive:

- Full frozen module surfaces/source authority already owned by the driver.
- Real diagnostic text arrays: promoted, then appended to the context after
  reclamation. Source diagnostics remain FAILED; cache/I/O failures block.
- Existing phase memo owners: package names and sibling names, surface/name
  indexes, reexport roots, dependency-target/item indexes, impl declaration
  positions and miss caches. These are surface/text/index lookup owners,
  not lowered HirModule/function-body collections. Their existing promotion
  owner is reused, not a shallow or guessed copy.
- Frontend registries through the existing generation-aware promotion owner;
  reverse-reference batches through the existing seal/end/publish protocol.
- Scalar completed surface IDs for alias deduplication.

The lowerer's module symbols, current scope, imported declaration caches,
current-function state and other scratch are detached by `begin_module` while
allocation is paused. Cache warning globals are cleared. Unused flat HIR rows
are rolled back before scope reclamation. No module symbol-table snapshot or
full HIR root is promoted for the shard. Nonshard behavior is unchanged.

If pause or root promotion fails, the flat row is rolled back, the owned scope
is aborted once, and the worker exits. It cannot continue with dangling memo
roots; the parent records incomplete infrastructure failure. Publication/end
failure never yields a successful ledger row.

## Required verification

Executable integration regression `hir_shard_scope_reclaim_spec.spl` performs:

1. Cold then warm native builds of three real modules with separate object
   caches and common authenticated HIR cache. Execute both outputs and check
   the cached function body returns37 and a sibling's imported record returns42.
   Require real successful shard receipts and final worker HIR cache hits.
2. Replace one known owned `.hir` entry with a directory after the warm run.
   Keep the cache root/queue writable, forcing the atomic entry publication to
   fail inside the transaction rather than during queue setup. Require its
   actual failure diagnostic, nonzero build and absent executable. No production
   failure-injection switch is introduced.

All three phases of this integration scenario are UNRUN. The three fixture files must be inside the admitted
derived source/SCV root. Run with a rebuilt pure-Simple producer under the
shared resource owner, requested80 codegen jobs and one frontend worker.
Do not run this environment-mutating integration suite concurrently with others.

A bounded patched-producer RSS/lifetime probe must record actual Job peak and
terminal evidence before claiming improvement. Retain old88 receipt/cache; no
cap increase, guessed allocation assertions or cache authority relabeling.
Nonstreaming HIR lifetime and final-worker whole-program retention remain
separate work; this change does not claim whole-bootstrap memory qualification.
