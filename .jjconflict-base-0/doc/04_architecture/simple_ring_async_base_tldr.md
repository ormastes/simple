<!-- codex-design -->
# Simple Ring and Async Base — TLDR

Status: **PROPOSED V1 architecture.** The document freezes boundaries and
contracts; it does not claim native-provider or compiler-lowering completion.

## Core decision

One typed data-plane contract and one stackless task ABI:

```text
typed AsyncTaskFrame/poll
  -> profile executor
  -> SimpleRing<Op, Cpl>
  -> software, OS, or device provider
```

Stable values (`SimpleRing`, `RingToken`, `RingGeneration`, `RingAdmission`,
`RingCompletion`, `RingMappingGrade`, `AsyncTaskFrame`, `TaskPollResult`,
`TaskContext`, `AsyncProfile`) live in
`src/lib/common/contracts/execution`.

## MDSOC ownership

- Hosted bounded ring/reference provider: `src/lib/nogc_async_mut/async_ring`.
- Mission allocation/static-pool adapters: `src/lib/nogc_async_mut_noalloc/async`.
- Existing Future/host compatibility: `src/lib/nogc_async_mut/async` and
  `async_host`; adapters cannot add a second ABI.
- Compiler: `src/compiler/00.common`, `20.hir`, and `50.mir` own effect/frame
  metadata only, not scheduling or ring storage.
- OS/SOSIX/device code owns policy/provider adapters and private descriptors;
  common contracts remain platform-neutral.

## Frozen semantics

Fixed-capacity reserve → commit transaction; explicit full/partial outcomes;
exactly one terminal completion; slot + generation stale rejection; explicit
ownership and cancellation; reset invalidation; exact task wake without global
task scans. `poll` is nonblocking and returns `Ready` or `Pending(wait_token)`.

## Profiles and operations

`common`, `script`, `server`, `mission_alloc`, and `mission_pool` select memory,
scheduler, mapping, assurance, instrumentation, placement, bounds, blocking,
fallback, detachment, and determinism. Each emits a fingerprint. Mission
profiles reject growth, hidden blocking, detached work, unknown bounds, and
silent fallback; `mission_pool` also rejects work stealing and heap after
`Ready`.

Startup validates the profile/provider and publishes its fingerprint. Reserve,
commit, completion, cancellation lookup, targeted wake, and ready insertion
are O(1); batch paths are O(batch size). Server/mission steady state has no
heap growth. Reset, provider identity, capacity, and profile changes invalidate
the relevant generation or capability cache.

## Next paths

Read the [full architecture](simple_ring_async_base.md), frozen lane state
(`.spipe/simple-ring-async-base/state.md`), selected requirements, and source
owners under `src/lib/common/contracts/execution/`,
`src/lib/nogc_async_mut/async/`, `src/lib/nogc_async_mut_noalloc/async/`,
`src/compiler/`, and `src/os/`.
