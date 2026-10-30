# Async infrastructure — TLDR

Simple already implements hosted futures/promises, scheduler task contexts,
embedded async, SimpleRing, and native I/O/fiber adapters. The design connects
and hardens those owners; it does not add another runtime.

- Shared interface: `std.async`; hosted implementation: `async_host`;
  bounded composition: proposed `std.embedded_async`.
  Preserve existing `async_host`, `async_embedded`, and `async_unified` aliases
  through a versioned, tested export migration.
- One canonical `TaskPollResult`/`RingToken` ABI; rings stay single-owner.
- Future/Promise, TaskHandle, AsyncRef, ResourceFactory, and IndexRefFactory
  have separate result, execution, creation, and lifetime responsibilities.
- Current gaps include detached pending chains/joins, discarded task-return
  publication, carrier-local wake paths, and incomplete strict-profile wiring.
- Lock-free scalar operations do not qualify typed allocations, generic
  payload lifetime, a sleeping executor, or the whole compiler.
- Native and future pure-Simple backends share interfaces/conformance;
  backend addresses and native value layouts remain private.
- [Collection capabilities](../compiler/collection_backend_capabilities.md)
  keep DataFrame/layout/profile selection consistent with the same resource
  contracts; static/no-capture/unsupported switching stays explicit.
- Resident hits avoid creation/I/O/global recency work. Frozen snapshot keys,
  retained ownership and exact invalidation remain required.
- TDD order: S1 async slots/I/O → S2 shared invoker/adapters → S3 immutable
  container/ref/cache storage. 3,000 requests do not mean 3,000 workers.

Read [architecture](async_infrastructure.md),
[detail design](../../05_design/lib/runtime/async_infrastructure.md), and
[test plan](../../03_plan/sys_test/async_infrastructure.md). Source audited at
`32b48baa7b4`; no native qualification or performance result is claimed.
