# Requirements — Simple Container Improvement

**Date:** 2026-11-25
**Status:** Selected. Options were presented and decided in the design
conversation consolidated into `doc/04_architecture/platform/container/simple_container_improvement.md`
§1 ("Decisions and priorities", "Selected architectural direction"); that table
is the user's selection record. Unchosen options were deleted per policy.

## Increment 1 (this change)

- REQ-001: Selectable content hashing with policies `xxh3-128` (default),
  `gxhash-128` (pinned profile `gxhash-4.0.0-scalar`), `blake3-256`, and legacy
  `sha256`; unknown selection fails closed; no algorithm's output is ever
  emitted under another algorithm's tag.
- REQ-002: Versioned immutable object records with digest aliases, decoupling
  lookup keys from authoritative object identity; strict decode with an invalid
  sentinel.
- REQ-003: Immutable object store with staged, read-back-verified, no-replace
  publication; concurrent-winner validation; collision-safe dedup (byte
  comparison before coalescing; distinct objects + collision records on
  digest collision).
- REQ-004: Root manifests published with generation compare-and-swap; retention
  pins; dry-run-first GC that moves unreachable objects to quarantine and never
  unlinks.
- REQ-005: Container capability report contract with fail-closed admission
  (architecture §4.2); a required capability is never silently weakened.
- REQ-006: Container lifecycle journal contract with strict codec and a pure,
  idempotent recovery-action planner (architecture §11.3–11.4).
- REQ-007: Legacy SCV compatibility: `sha256_<hex>` identities remain valid
  object keys/aliases; no change to existing SCV behavior or formats.

## Later increments (planned, not claimed)

Architecture phases 2–5: real container storage/isolation/limits/cleanup on
native providers, canonical backing + SimpleOS shared pages, provider
qualification (Windows/FreeBSD/macOS/SimpleOS), measured optimization and agent
lifecycle. See the architecture §16 implementation plan.

## NFR

- NFR-001: All new code pure Simple under `src/lib/`; no new dependencies.
- NFR-002: Every public function returns an outcome struct or reason text; no
  panics on hostile input; checked arithmetic on lengths; bounded collision
  scan (n ≤ 64) and bounded no-follow reads.
- NFR-003: SDN by default for records, roots, pins, and collision records.
- NFR-004: Unit specs with real assertions for every module; one SPipe system
  spec with generated manual; no placeholder passes.
