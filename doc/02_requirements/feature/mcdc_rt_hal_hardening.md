# Requirements: MC/DC, RT, and HAL Hardening

Date: 2026-08-25
Selected option: C — Full integrated feature

- REQ-001: Provide statically disabled, statically enabled, and dynamically
  aspect-loaded MC/DC modes. Static disablement emits no probe, state,
  registration, allocation, dispatch, or loader dependency on covered paths.
- REQ-002: Preserve evaluation order/count, short-circuiting, side effects,
  results, and exceptions while recording true/false/not-evaluated condition
  occurrences with deterministic decision identities.
- REQ-003: Compute exact masking MC/DC, retaining unique-cause evidence where
  possible and explicitly reporting strong coupling and the applied policy.
- REQ-004: Use bounded owner-local recording with explicit drop/overwrite state,
  deterministic parent-authoritative aggregation, and no global hot-path lock.
- REQ-005: Normal and stricter modes require exact 100% MC/DC after approved
  exclusions and fail with stable machine/human diagnostics otherwise.
- REQ-006: An exclusion is narrowly scoped and requires a stable identity,
  non-empty technical reason, and review metadata. Invalid, stale, broad, or
  reasonless exclusions fail and never count as covered or skipped PASS.
- REQ-007: Dynamic loading activates/deactivates MC/DC without rebuilding the
  instrumentable program and performs no per-decision allocation after bounded
  initialization. Unsupported targets fail closed or use a documented inert
  fallback without claiming zero-cost patchpoints.
- REQ-008: Define a configurable `rt(hal)` provider contract for Pure Simple, C,
  and Rust. Pure Simple remains the semantic/product owner; foreign providers are
  optional comparators and never replace it.
- REQ-009: Canonicalize HAL requests, results, errors, and observable effects.
  Queries may compare concurrently through bounded workers; destructive effects
  execute exactly once and compare by deterministic trace/replay.
- REQ-010: Express RT/HAL test interactions as typed bounded environment-access
  instructions. Environment executors return receipts and reject undeclared or
  unsafe work; test leaf modules do not directly read environment/run processes.
- REQ-011: Unavailable environments report typed BLOCKED/UNSUPPORTED evidence
  with reason, prerequisite, owner, artifacts, and resume command, never PASS.
- REQ-012: RT declarations default to mission-critical unless explicitly
  annotated. Legacy implicit declarations receive one actionable warning phase,
  followed by the same stable condition becoming a compile error.
- REQ-013: Mission-critical transitive closures reject unbounded allocation,
  blocking, recursion/loops, dispatch, logging, synchronization, and loader work
  unless a reviewed capability proves an applicable bound.
- REQ-014: Interpreter/native results, concurrent aggregation, provider ordering,
  and repeated-build identities are deterministic.
- REQ-015: Public behavior/API remains compatible except for explicitly staged
  safety diagnostics and new opt-in configuration surfaces.
