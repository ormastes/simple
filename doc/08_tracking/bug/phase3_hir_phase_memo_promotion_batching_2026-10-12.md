# Phase-wide HIR memo promotion repeats reachability walks

Status: focused source repair; native lifecycle and aggregate performance
validation pending. No RSS or elapsed-time improvement is claimed.

The frozen attempt-3 CLI build at source HEAD
`0e44a375a47985e6a3b7974a9378c694d5c888e3` parsed, committed and released all
2549 declaration surfaces. Its subsequent `hir-reexport` warnings occur during
HIR lowering, rather than proving a dependency-freeze stall. The log contains
`hir` progress at 626/2549 and elapsed 1590406 ms. Log location:
`build/bootstrap/stage2-compiler-tests/x86_64-pc-windows-msvc/verification/logs/compiler_cli_build.log`.
Warning frequency alone cannot attribute time or retained memory to reexport
resolution; no warning suppression or nominal-container exclusion is proposed.

`HirLowering.promote_phase_memo_transient_owners` promotes 49 collection owners
separately after every transient HIR scope, plus one guarded scalar text owner.
These owners include both dictionary and scalar-chain representations of growing
phase memos. In `src/runtime/runtime_native.c`, `rt_transient_heap_promote`
classifies persistent arrays/dictionaries as traversable, visits their children,
and builds a fresh traversal plan and seen set for each call. It frees that plan
before returning. This proves repeated graph traversal, not a retained plan leak
or a measured cause of the observed RSS growth.

The repair follows the existing `ModuleSurfaceRoot` pattern: 49 exact typed
owners become enum payloads in one root array. One collection promotion walk
can deduplicate shared children across the batch; the conditional scalar text
call remains separate because the empty literal can be unregistered. The
lowerer still owns the original memo fields across scope resets. No entire
lowerer, symbol table, provider registry, module-local scratch or diagnostics
graph is added to the root set. The carrier array is shallow-freed after either
provider success or refusal, and the provider result still propagates to the
driver's existing fail-closed path. Promotion refusal can now leave fewer
partially promoted collection owners, but cannot become success.

This pattern also promotes its enum wrappers. The native shallow array-free
operation frees only the carrier; wrappers have no enum-free API. Therefore
the patch adds 49 small persistent wrappers per call, as the existing surface
pattern does. It is a traversal optimization with an unmeasured carrier-memory
tradeoff. Aggregate RSS improvement must not be inferred from the call count.

Static evidence under
`C:/dev/simple-phase3-hir-memory-evidence/phase-memo-batching/source-root-parity.txt`
compares the original method in the frozen checkout to the private repair:
all 50 owners remain, 49 batch payload types exactly match field declarations,
and no collection owner is missing or duplicated. The collection call budget
is 49 to 1, with scalar behavior unchanged. Working and staged direct-env
guards and `git diff --check` are required before exporting the patch.

The enum and promotion helper live in the dependency-free
`compiler.hir.hir_lowering.phase_memo_ownership` module. `types.spl` imports
that module, preserving the root set and driver failure behavior. The lifetime
spec imports the small helper directly, rather than importing `HirLowering`
and the parser/provider graph. Its boolean checks use the allowed
`to_equal(true/false)` matchers.

The source regression pins original owners, exclusions, scalar guard and
failure propagation. The native lifetime spec covers all seven payload families,
repeated aliases, reads after scope release, second-scope dictionary growth and
refusal without an active scope. The standalone fixture
`test/fixtures/compiler/phase_memo_ownership/main.spl` covers those contracts
without SSpec allocations inside active transient scopes. It includes shared
array payloads, a dynamically allocated string, 64 new dictionary keys in the
second scope, and refusal before and after the active scopes. Its 25 positive
guards increment a receipt counter and emit
`phase memo ownership: 25 checks passed` only after all succeed; each failure
has a distinct nonzero exit code.

Neither Simple spec nor the fixture has been executed for this patch. Native
execution must use a real Pure-Simple producer and bind runtime/provider and
source identities; interpreter extern stubs are not acceptable evidence.
No native job was launched while the frozen compiler matrix remained active.

## Attempt-3 terminal evidence

The full CLI streaming run terminated with RSS failure, exit 88, after 2506
seconds. Its last completed HIR progress was 1335/2549; the next current module
was `compiler.backend.backend.native.mod`. The watchdog recorded
`peak_rss_kib=5965372`, `rss_limit_kib=5859375`,
`peak_job_commit_kib=6220304` and `quiescent=1`. The CLI artifact was marked
`producer-failed`; no full CLI executable or suite qualification resulted.
The previous retained-parser campaign stopped at HIR 85/2545. Streaming reached
more modules in this campaign, but the producer/source inventory and other
repairs differ, so this comparison is not an isolated memory benchmark.
Batching was not present in either run and remains an unmeasured optimization,
not an established repair for the terminal RSS failure.

The frozen log contains 2549 distinct `parse-done` paths. Applying the canonical
module-name algorithm, including its nested `/src/` handling, yields 2549
distinct logical names. All 1335 distinct completed HIR names belong to that
inventory. The three tracked Windows directory junctions account for 29 source
paths; their resolved example targets are not also admitted under other paths.
The junction-resolved path count remains 2549, with no duplicate path groups.
This is a path/junction census, not a Windows file-ID proof. Equal source bytes
are not permission to coalesce independently admitted modules.

The exact completed-HIR cache directory is
`build/bootstrap/stage2-compiler-tests/x86_64-pc-windows-msvc/cache/compiler-tools/stage2/17d1a40abc390c08c05cec3ba13db41eb12ee5709126c6636fe974f753f7e5ac/3c2f768ef33d6945f41337dc8ed2934bda7e141d4120b12729bd0aa71e02c592/full-cli/hir`.
It contains exactly 1335 `.hir` files totaling 545375774 bytes. The largest is
`formula.spl`, 4383356 bytes. Read-only decoding of the eight largest artifact
prefixes found 3004–7581 symbol records per module; `driver_types.spl` has 7581,
and `formula.spl` has 4434. These counts do not distinguish imported signatures
from local symbols. Serialized bytes repeat shared type references and are not
a native retained-memory estimate.

Retained evidence lives under
`C:/dev/simple-phase3-hir-memory-evidence/phase-memo-batching/`:
`attempt3-cli-terminal-tail.log`, `attempt3-cli-inventory-counts.json`,
`attempt3-cli-admitted-physical-logical.csv`, `attempt3-cli-completed-hir.csv`,
`attempt3-cli-cache-metadata.json` and `attempt3-cli-largest-cache-prefixes.json`.
No root source, compiler process or cache artifact was changed during collection.

## Remaining retention boundary

The concrete source policy retains all completed bodies through the full HIR
phase. `driver_hir_pipeline_lowering.spl:945` stores every complete `HirModule`
in `lowered_by_surface`, then `phase_hir_modules`. Repeated surface indices
reuse that same graph at line 681. `SymbolTable.module_snapshot()` in
`hir_types.spl:357` creates a distinct owner referencing the module's existing
containers; it does not copy a full provider table. The layout view in
`value_struct_layout.spl:23` retains structs and Struct symbols only. Importer
registration, trait, enum and callable-tail scratch is reset by
`context_helpers.spl:70`. No additional cloned whole-provider leak was proven.

`driver_aot_pipeline.spl:118` calls `evict_hir()` only after all MIR lowering.
`driver_types.spl:1461` merely replaces the HIR map and entry alias. On the
no-GC C runtime, promotion makes objects persistent; removing an owner is not
an explicit reclaim operation. Thus activating the existing eviction flag
cannot bound the peak during HIR or reclaim already-promoted body graphs.
The relative share of necessary bodies, symbol/type graphs, phase memos and
other allocations in the observed RSS is still unmeasured.

Existing persistence supplies reusable boundaries, but no existing activation
offers bounded completed-HIR retention for this full semantic path:

- `driver_hir_cache.spl:136` binds keys to physical source/path, complete frozen
  surface closure, entry role, semantic switches and codec. Its header at
  line 154 binds the frontend producer/source scope, and loading checks header,
  checksum, framing and decoding. `hir_cache_load()` at line 197 promotes the
  full decoded graph, so repeatedly using it still accumulates persistent HIR.
- `hir_cache_store_in_owned_scope()` at line 358 can persist a module inside a
  caller-owned scope. `hir_cache_load_in_owned_scope()` at line 217 already
  supports shard-owned decoding without promoting the full graph. These are
  suitable primitives for a bounded body lease, with actual scope closure
  reclaiming the unpromoted body and scratch.
- `cold_hir_semantic_seed_v1.spl:29` retains compact typed ABI receipts after
  HIR eviction. Its admitted-digest receipt boundary at line 144 validates
  physical source identity and inventory. Current receipt capture at
  `driver_hir_pipeline_lowering.spl:1048` happens after the whole HIR loop,
  too late to release completed bodies during that loop.
- `cold_hir_native_object_persistence_v1.spl:24` requires complete module
  coverage, accepted capsule identities and objectless classifications; it
  validates object bytes, digest and capsule receipt before CAS publication,
  retaining only compact artifact identities. Warm group admission in
  `native_group_warm_route.spl:259` checks producer, variants, SCV/full-source
  authority, target, SCC membership and archive admissions.
- `cold_full_index_retention_v1.spl:1` explicitly trims only after the full
  semantic pass. It does not solve that pass's peak. Method resolution and
  monomorphization in `driver_hir_pipeline_passes.spl:45` and line 127 still
  consume/mutate the complete HIR map.

The missing feature is a leased HIR store and semantic consumer interface:
persist real bodies inside per-module scopes before promoting only their
declaration/layout/global summaries and typed receipts; keep the admitted full
source inventory and configured selection resident; hydrate a module and its
required generic/dependency bodies into a bounded scope for every semantic
consumer; persist transformations before ending that scope. Type checking,
method resolution, monomorphization, warning/contract passes and layout
validation must retain their actual diagnostics and global summaries. A map
replacement alone is insufficient. The artifact/lease identity must additionally
bind the exact linked runtime/provider and target selections; the current HIR
header alone does not establish all those bindings. Missing bodies, admission
failures or oversized required dependency groups must fail closed, not select
stub providers, omit sources or increase the campaign cap.

The finite next boundary is the pending 25-guard lightweight native lifetime
fixture, followed by a scoped persistence/hydration prototype and its negative
identity and aggregate-semantic contracts on a pinned Pure-Simple producer.
No such prototype is implemented here. An identical full CLI restart is not a
diagnostic for this ownership gap; batching alone does not justify repeating it.
Other reviewed compiler fixes still require their own next-producer tests.
