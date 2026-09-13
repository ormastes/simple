# i18n duplicate module coverage identity

**Status:** OPEN (unverified 2026-09-12)

`src/lib/nogc_sync_mut/i18n/bundle.spl` and
`src/std/nogc_sync_mut/i18n/bundle.spl` are byte-identical production copies.
The same applies to `global.spl`.

A direct 13-example production suite executed bundle methods successfully.
When both paths were instrumented, all hits mapped to `src/lib` (50/95 lines,
13/14 branches); the `src/std` path reported 0/95 lines and 0/0 decisions.

This prevents trustworthy aggregate all-owner coverage and creates divergence
risk. Select one authoritative implementation, convert the other path to a
thin compatibility re-export, and canonicalize coverage source identities.

## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
