# Aspect-seal census stack-overflows — Phase 6 exit gate is dead, not green

**Date:** 2026-08-24
**Severity:** HIGH (a hardening exit gate reports ERROR, and its last recorded PASS is unreproducible)
**Status:** OPEN
**Plan section:** hardening plan Phase 6 (`doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`)

## Symptom

`sh scripts/check/check-aspect-seal.shs` exits **2**:

```
ERROR — nothing was checked (selftest failed: positive-fixture-produced-no-summary
  unbound-required-not-detected duplicate-binding-not-detected
  late-activation-not-detected unverified-signature-not-detected)
```

All five fixtures fail at once, which is the signature of the driver dying
rather than of five independent detection defects.

## Root cause (reproduced directly)

The census driver aborts on the currently deployed compiler:

```console
$ bin/simple run src/app/check/aspect_seal_census.spl --critical \
      --aspect test/fixtures/aspect_seal/audit_trace_clean.sdn
thread 'simple-main' (2121154) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

With no `--aspect` argument the same driver runs to completion
(`SUMMARY aspects=0 ... parse_fail=0`), so the fault is on the aspect-parsing
path, not in startup.

## Binary identity

```
bin/simple -> bin/release/x86_64-unknown-linux-gnu/simple
60650360 bytes, 2026-08-23 04:47:05 UTC, sha256 f6521b60b67d3894…
--version: Rust bootstrap SEED warning banner present
```

The Phase 6 PASS recorded on 2026-08-21 was minted against artifact
`5d35debcec323548…` — a different binary. The fixtures themselves are
unchanged since the landing commit `1df56d314f5` (`test/fixtures/aspect_seal/`,
mtime 2026-08-21 06:33), so the change is on the compiler side.

## Why this matters beyond one gate

`check-aspect-seal` is a required Phase 9 release obligation
(`scripts/check/critical_release_required_receipts.txt`). Because the gate
ERRORs it mints no fresh receipt, so `check-critical-release-seal.shs` reports
the obligation as stale. That is the fail-closed behaviour working — but it
means the aspect half of §22.4 currently has **no executable evidence at all**,
and the plan text still describes it as landed and green.

## Not yet determined

- Whether the overflow is unbounded recursion in the census's own SDN walk or in
  the seed's parser/interpreter. Both are plausible; nothing here decides it.
- Whether a pure-Simple (non-seed) binary reproduces it. `bin/simple` is the
  Rust seed today, so the run above is seed evidence only.

## Resume

- **Owner:** Phase 6 aspect lane.
- **Prerequisite:** none for diagnosis; a pure-Simple redeploy for the parity half.
- **Command:** `bin/simple run src/app/check/aspect_seal_census.spl --critical --aspect test/fixtures/aspect_seal/audit_trace_clean.sdn`
- **Done when:** `sh scripts/check/check-aspect-seal.shs` exits 0 and
  `sh scripts/check/refresh-critical-release-receipts.shs --only check-aspect-seal`
  reports the obligation fresh.
