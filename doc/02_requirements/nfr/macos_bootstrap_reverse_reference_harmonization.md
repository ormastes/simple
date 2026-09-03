<!-- codex-research -->
# macOS Bootstrap Reverse-Reference Harmonization NFRs

Status: SELECTED.

Decision source: user-final-performance-authority-2026-09-02

- **MBH-NFR-001 — Determinism.** Clean and compatible-reuse outputs shall be
  byte-identical, or identical after a documented normalization of unavoidable
  nondeterministic fields.
- **MBH-NFR-002 — Incremental no-op.** A valid warm no-op shall parse, lower,
  and emit zero modules where producer-neutral caches apply, and shall not link
  when the ordered link-input receipt is unchanged. Admission shall happen
  before parser/HIR/MIR/codegen/link scheduling, bind the canonical complete
  build request and requested-input identity, and recursively authenticate the
  complete immutable receipt ancestry. Missing, corrupt, cyclic, or excessive
  ancestry, stale invocations, and unrecoverable generation collisions fail
  closed. One centralized schema shall classify every environment field read by
  native-build owners, hash every semantic field, and reject unknown or omitted
  schema fields; representative no-mangle, package-index, safety/type-profile,
  backend/linker, provider, and bootstrap controls shall be mutation-tested.
  When environment enumeration is available, identity shall additionally hash
  a sorted presence-aware snapshot of every present `SIMPLE_*` control. A
  repository-wide owned-code registry audit shall fail when any new literal
  environment read appears before its compile impact is reviewed. Only
  diagnostics/cache destinations and temporary staging locations proven not to
  affect artifact bytes may omit explicit absent rows.
- **MBH-NFR-003 — Bounded residency.** Evidence shall record wall time, CPU,
  peak/retained RSS, cache counts, and critical path. Each architecture shall
  supply an admitted baseline receipt bound to that architecture, its baseline
  evidence digest, the producer and server digests, the final user decision
  source, and this document digest. Across exactly 20 warm requests, maximum
  steady RSS shall be at most 110% of baseline RSS and nonnegative RSS growth
  shall be at most 10% of baseline RSS. Missing, shared, inferred, stale, or
  unbound baselines fail closed.
- **MBH-NFR-004 — Integrity.** All admitted artifacts and reuse decisions shall
  carry cryptographic digests and durable provenance. Any mismatch shall fail
  closed with a stable reason code.
- **MBH-NFR-005 — Native evidence.** Architecture, Mach-O load commands,
  provider archives, deployment target, SDK, compiler, and per-slice hashes
  shall be captured from the executing native runner.
- **MBH-NFR-006 — Concurrency safety.** Shared publication, when introduced,
  shall prove identical/conflicting writers, pinned readers, crash recovery,
  and lease-aware garbage collection before enabling shared mutable state.
