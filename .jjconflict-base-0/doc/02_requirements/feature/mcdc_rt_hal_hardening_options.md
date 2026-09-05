# Feature Options: MC/DC, RT, and HAL Hardening

Date: 2026-08-25. Selection is required before design/implementation.

## A — Compiler MC/DC only

Native semantics-preserving MC/DC, bounded evidence, exact reporting, and reasoned
exclusions.

- Pros: smallest coherent safety increment; replaces unsafe rewriting.
- Cons: defers RT defaults, environment receipts, HAL comparison, and dynload.
- Effort: high, 6–10 engineer-weeks.

## B — Integrated static safety profile

Option A plus mission-critical RT defaults/staging, typed environment receipts,
governed skips, and a common Pure Simple/C/Rust HAL comparison contract. Supports
static off/on; dynamic activation is designed but deferred.

- Pros: coherent evidence contract and lower delivery risk than runtime patching.
- Cons: does not meet live dynamic-aspect activation.
- Effort: very high, 12–18 engineer-weeks.

## C — Full integrated feature (recommended)

Option B plus dynamically loadable MC/DC aspects, dormant low-overhead activation,
bounded owner-local recording, deterministic parallel query comparison,
execute-once trace/replay, and configurable provider sets. Pure Simple stays the
semantic/product owner; C/Rust remain optional comparators.

- Pros: fulfills the complete request through reviewable milestones.
- Cons: largest compiler/runtime/API change; some targets need an inert indirect
  branch fallback where safe patchpoints are unavailable.
- Effort: exceptional, 20–30 engineer-weeks.

All options preserve evaluation semantics, require exact condition occurrences and
reasoned exclusions, prohibit unbounded evidence, require normal+ 100% after
approved exclusions, and report unavailable hardware as BLOCKED rather than PASS.
