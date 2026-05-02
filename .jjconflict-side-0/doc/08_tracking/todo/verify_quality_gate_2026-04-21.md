# Verify Quality Gate

**Date:** 2026-04-21
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 193
**Status:** Closed

## Research

- Row 193 asked to integrate the anti-dummy / anti-stub quality gate into the stable user-facing verify path.
- `bin/simple --help` advertises `simple verify quality [--all] [file ...]`.
- `bin/simple verify quality --help` returns the expected usage.
- `doc/08_tracking/anti_dummy_stub_backlog_2026-04-04.md` already states the feature is implemented on `simple lint` and `simple verify quality`; remaining work is backlog migration debt.

## Plan

- Verify the stable command surface is present.
- Verify a clean spec exits successfully.
- Verify a placeholder-only spec fails with an anti-dummy finding.
- Close row 193 as stale completed tracking.

## Fix

- Closed `todo_db.sdn` row 193.

## Verification

```sh
bin/simple --help
bin/simple verify quality --help
bin/simple verify quality /tmp/simple_verify_quality_clean_spec.spl
bin/simple verify quality /tmp/simple_verify_quality_bad_spec.spl
```

Observed:

- Clean spec exited `0` and printed `Verify quality passed`.
- Placeholder spec exited `1` and reported `SPIPE005`.
