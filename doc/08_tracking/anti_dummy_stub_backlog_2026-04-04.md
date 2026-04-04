# Anti-Dummy / Anti-Stub Backlog

**Date:** 2026-04-04  
**Status:** Active cleanup backlog

## Snapshot

Current grep-based backlog for placeholder patterns in `test/`:

- total placeholder-pattern matches: **1070**

Patterns counted:

- `pass_todo`
- `pass_do_nothing`
- `pass_dn`
- `expect(true).to_equal(true)`
- `expect(false).to_equal(false)`

## Highest-Concentration Areas

Top path buckets from the 2026-04-04 audit:

- `test/feature/usage` — 157
- `test/unit/lib` — 143
- `test/system/compiler` — 89
- `test/unit/compiler` — 89
- `test/integration/t32_hw` — 62
- `test/integration/lib` — 50
- `test/integration/compiler` — 41
- `test/integration/baremetal` — 40
- `test/integration/sffi` — 38
- `test/unit/app` — 36

## Cleanup Strategy

### P1

- current-change enforcement via the verify/lint gate
- remove net-new placeholder debt

### P2

- clean placeholder-heavy hardware/T32/SFFI suites where tautologies currently mask capability-only checks
- replace fake success assertions with:
  - real result assertions
  - explicit capability checks
  - sanctioned skip behavior

### P3

- clean broad legacy buckets such as `test/feature/usage`, `test/unit/lib`, and `test/system/compiler`
- add mutation-style hardening to high-value suites after the placeholder baseline is lower

## Status Rule

The anti-dummy / anti-stub feature is now implemented on the primary CLI surfaces:

1. `simple lint`
2. `simple verify quality`

The backlog below is now migration debt, not missing detector functionality.

The repo can only claim universal anti-dummy cleanliness after:

1. legacy placeholder-heavy suites are migrated or intentionally exempted,
2. remaining production placeholders in OS/GPU/userlib paths are either implemented or quarantined,
3. backlog measurement is kept current from one reproducible command/report.
