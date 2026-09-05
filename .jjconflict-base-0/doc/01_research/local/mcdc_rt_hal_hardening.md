# Local Research: MC/DC, RT, and HAL Hardening

Date: 2026-08-25

## Findings

- Compiler coverage is a Boolean switch. Interpreter probes count evaluated
  decisions/conditions but do not prove independent influence. MIR models probes,
  while production backends reject them as unlowered.
- Current MC/DC is a source rewriter plus `nogc_sync_mut/mcdc.spl`. It eagerly
  evaluates atoms, can change short-circuit/side-effect/exception behavior, keeps
  unbounded evidence, and uses a quadratic independence-pair search.
- C coverage copies file names and linearly searches under a global mutex per
  hit. Rust locks a global map and allocates a string per hit.
- AOP recognizes static, dynload, and live-reload modes, but only static works;
  no MC/DC aspect activation or dormant patchpoint exists.
- No implemented `rt(hal)` provider tag exists. Native provider choice is link-time
  C symbol ownership. The small Pure Simple HAL has hosted IRQ/DMA success/no-op
  stubs; QEMU mock writes rebuild arrays and can become quadratic.
- Existing counterpart evidence infrastructure supplies provider identity,
  availability, timeout/crash, and bounded-output concepts, but successful sample
  envelopes are stubs and no canonical HAL effect schema exists.
- RT checks cover a narrow forbidden-I/O manifest only for explicitly realtime,
  interrupt, or no-allocation contexts. There is no criticality enum/default or
  warning-to-error migration.
- Environment facades and receipt examples exist. However, several tests turn
  missing hardware into passing assertions. Skip APIs require reasons/references,
  but their checker misses the actual DSL and the tracking directory is absent.

## Architecture consequences

1. Create stable decision and condition-occurrence identities before lowering;
   record true, false, or not-evaluated without forcing operands.
2. Compile static-off instrumentation away. Static-on and dynamic modes share a
   bounded binary record format and exact report semantics.
3. Use preallocated owner-local buffers, explicit overflow counters, deferred I/O,
   and indexed O(E*C) analysis instead of O(E²*C) pair scans.
4. Define one typed HAL request/result/error/effect contract. Queries may fan out;
   destructive work executes once and is compared via deterministic trace/replay.
5. Define typed environment instructions and receipts. Missing hardware is BLOCKED,
   never PASS.
6. Model criticality explicitly. RT defaults to mission-critical unless annotated,
   with one warning phase followed by an error phase.
7. Reject allocation, blocking, unbounded recursion/loops, unsafe synchronization,
   and unbounded dispatch in mission-critical transitive closures unless bounded by
   a reviewed capability.

## Performance review targets

Measure complexity, locks, allocations/copies, data locality, dispatch, text size,
latency, throughput, and peak RSS on the same before/after fixture. Preserve the
coverage inventory, MIR probe model, environment facade, skip governance,
counterpart registry, and frozen HAL design rather than duplicating them.
