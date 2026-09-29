<!-- codex-design -->
# Agent Tasks — Aspect Registry Transaction

## Frozen contract

All agents use the exact types, APIs, steps, helpers, and fail-fast placeholders
in the architecture and detail design. No parallel registry, lock, cache owner,
pin representation, or path-reopen API may be introduced. Agents use isolated
worktrees/caches and return exact file manifests. They do not commit, deploy,
push, or bootstrap; `/root` is merge owner.

## Parallel lanes

| Lane | Owner scope | Dependency | Required evidence |
|---|---|---|---|
| RT-1 registry core | `aspect_runtime_registry.spl`: mutex, slots, snapshots, counters, pins, quiesce transitions | frozen types | transition/mutation tests |
| RT-2 file snapshot/cache | `pack_file_snapshot.spl`, adapted `aspect_pack_index_cache.spl`: descriptor, identity/digests, lazy reads/maps, LRU | snapshot API | path-swap/no-reopen tests |
| RT-3 staging/mapper | `aspect_activation_transaction.spl`, adapted `segment_mapper.spl`: four classes, reloc journal, W^X, pre-publish rollback | RT-2 | injected-stage rollback |
| RT-4 registration/facets | adapters construct records and call publish; no registry mutation | RT-1/RT-3 | ambiguity/publication tests |
| RT-5 single-flight/context | registry waiter operations plus `aspect_dependency_stack.spl`; no pin ownership | RT-1 | real concurrency/cycle tests |
| RT-6 retirement executor | consumes registry batches, sidecar drop/unmap/close, then calls only `aspect_registry_retirement_complete` or `aspect_registry_retirement_poison`; no direct registry mutation | RT-1/RT-3 | ABA and full-unmap tests |
| RT-7 startup/JIT adapters | eager/lazy roots, symbol snapshot consumption | RT-4/RT-6 | startup and invocation tests |
| RT-8 system/manual | frozen helpers, negative controls, generated manual | integrated candidate | zero-stub SPipe/manual |
| RT-9 performance | lock/open/cache/cold/warm metrics and budgets | integrated candidate | retained receipts |

Lower-model sidecars: Codex Spark may inventory legacy dictionary/path reopen
callers for RT-2/RT-7; Claude Haiku may compare generated schema/manifest files;
Claude Sonnet may review manual readability. They may not decide lock ordering,
publication, pin/ABA, rollback, native retirement, or done status.

## Merge and review order

1. `/root` freezes RT-1 types and RT-2 snapshot interfaces.
2. Merge RT-1 and RT-2, then RT-3.
3. Merge RT-4 and RT-5 against those owners.
4. Merge RT-6 before startup/JIT adapters.
5. RT-8 and RT-9 validate only the integrated candidate.
6. A separate highest-capability reviewer inspects every registry mutation,
   lock boundary, publish trace, rollback edge, immutable-byte use, pin
   transition, and mutation control; it returns GO/HOLD with file evidence.

## Mandatory handoff

- One registry mutex protects every named mutable field.
- No blocking/unsafe/heavy work happens under it.
- Staging is off-registry; Active is final record initialization and snapshot
  installation is the visibility mutation.
- Waiters share one immutable attempt result; retry is explicit.
- Reader snapshots require nonce-bearing generation pins before invocation.
- Dependency stack is execution-context local and unwinds on every path.
- Rollback/unload accounts for Code/Data/RoData/BSS, symbols, relocations,
  witnesses, sidecars, handles, pins, and snapshot leases.
- Partial retirement is poisoned and cannot masquerade as success.
- All lazy reads/maps use the originally opened descriptor; no path reopen.
- Fail-fast placeholders remain red until replaced by production-backed oracles.
- `/root` alone commits and declares the lane complete after highest-model GO.
