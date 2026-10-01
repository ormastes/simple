# Bootstrap collect-all recovery

## Existing ownership

`app.cli.native_build_main` supervises worker processes through `app.io.mod`.
`compiler.driver.driver_hir_cache` owns HIR cache identity and shard claims.
`compiler.driver.driver_hir_pipeline_lowering` owns the module boundary and knows
whether lowering completed, emitted diagnostics, or was blocked. Environment
and process access remains behind the existing SOSIX/application facades.

The current shard queue is a cache warmer: children claim modules, the coordinator
waits and removes the queue, then the final worker lowers every cache miss. A
crashed module can therefore be retried in the final worker while later modules
remain unattempted. The recovery protocol makes this failure terminal for the
invocation and gives replacements access to the remaining queue.

## Shared contract

`run_hir_shards(...) -> i64` returns an aggregate exit status. Its caller must
return nonzero before launching the final worker or exposing a candidate when
the shard pass failed.

`compiler.driver.driver_hir_recovery` owns deterministic decision helpers:

- `hir_shard_recovery_can_replace(fail_fast, exit_code, new_claims) -> bool`
- `hir_shard_aggregate_exit(failed_workers, failed_modules) -> i64`

Replacement requires collect-all mode, a nonzero worker exit, and at least one
new module claim. Progress includes a terminal diagnostic when a worker reaches
its poison budget before finishing the inventory. A completed-traversal receipt
distinguishes that case from an exhausted inventory. A successful worker is not a crash replacement. A
preflight failure without a module claim is terminal for that worker. The process
owner additionally honors explicit global prerequisite/guard failures, which
must never be interpreted as module-local recoverable failures.

Before claims, workers publish and agree on the frozen physical source inventory.
An active shard without an established HIR cache identity fails before normal
pipeline work; it cannot silently become a final worker. Before risky module
work, the driver publishes an invocation-local record with
the worker owner, source identity, cache key, and active state. Normal completion
or diagnostics seals it. When a worker exits unexpectedly, the supervisor seals
that owner's active records as crashed; terminal records are never reopened.
Every replacement consumes at least one previously unseen module, providing a
finite bound from the frozen module inventory. Invocation records are not cache
entries and do not redefine compilation identity.

The coordinator closes the frozen inventory after all children are confirmed
stopped. Unvisited modules become `BLOCKED` in collect-all mode or `SKIPPED` under
fail-fast. Wait result `-1` is an error and `-2` is a timeout; neither proves a
child was reaped. Uncertain worker liveness prevents claim sealing and inventory
closure, preserving the active evidence and failing the aggregate.

The canonical policy is `SIMPLE_COMPILE_FAIL_FAST`, defaulting to collect-all on
the host and fail-fast in CI. Explicit CLI `--keep-going`/`--fail-fast` flags
override environment/default policy in their original order; the last wins.
The coordinator forwards that resolved policy to replacement workers.

Successful lowering and reusable cache evidence are distinct. A codec that does
not support a valid module already returns no cache entry; preserving that
behavior requires an explicit uncached completion, not a false cache hit. The
final worker may re-lower such modules only after a failure-free shard pass.

## Cache validity and invalidation

Retain `spl-hircache-v2` and its existing codec. The key folds source SHA-256,
the digest of **all** frozen module surfaces and aliases, entry/module role,
lowering environment switches, and codec header. The entry header additionally
binds the frontend cache scope, including the producing compiler identity.
Changing an unrelated surface can affect declaration ownership, so a narrower
import-only digest is invalid.

`hir_cache_has` historically validates only the header. Recovery must not count
that as validated reusable HIR: `hir_cache_load` also checks warning framing and
decodes the body. Truncated or corrupt entries remain misses. Atomic cache stores
and warning replay remain owned by the cache implementation. Retrying preserves
successful entries and never clears a whole cache to address one failed module.

## Failure boundaries

Frozen surfaces allow independent HIR work without another module's HIR output.
Semantic poison/dependency checks still determine whether a module is safely
processable. Fail-fast stops additional scheduling; collect-all consumes safe
remaining work. Neither policy converts diagnostics or process failures into a
successful artifact. Spawn, claim publication, and global preflight failures
remain explicit failures even when no module can be attributed.

No process fault is recovered inside the crashed address space. Recovery occurs
in the parent supervisor by starting a fresh child. Source-only checks are useful
for gate placement but do not establish runtime crash recovery.
