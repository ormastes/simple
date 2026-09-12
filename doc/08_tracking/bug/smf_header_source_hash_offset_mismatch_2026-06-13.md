# BUG: SMF header `source_hash` write/read offset mismatch (68 vs 84)
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- **ID:** `smf_header_source_hash_offset_mismatch`
- **Severity:** P2 (latent — user-script SMF cache validator may read the wrong bytes)
- **Found:** 2026-06-13, perf-umbrella Lane B (AC-7 dynSMF cache work, while confirming the
  existing `simple run` content-hash path — out of AC-7 scope, recorded not fixed).

## Symptom
- `src/.../smf_header.spl` `to_bytes()` writes `source_hash` at header offset **68**.
- `src/compiler/.../cache_validator.spl` (`validate_smf_with_deps`, ~line 103) reads the
  embedded source-hash field at `header_start + 84`.
A 16-byte discrepancy. If both paths are exercised, the validator compares the wrong bytes,
which could make the unchanged-script cache either falsely hit or falsely miss.

## Why it may be masked today
The user-script cache also hashes the source via `rt_hash_text` and may short-circuit before
the offset-84 read matters, so the latent mismatch has not produced an obvious failure.

## Impact
- Risk to AC-7's "unchanged-script cache reuse" correctness for the `simple run` lane (the
  lane AC-7 deliberately did NOT modify). The new dynSMF lane uses a `.srchash` sidecar and
  is unaffected.

## Proposed next step
Pick one canonical offset for `source_hash`; make `to_bytes()` writer and `cache_validator`
reader agree; add a round-trip spec (`write header → read field → equal`).

## Status
OPEN — recorded. Out of AC-7 scope (sidecar lane unaffected). Validate before relying on the
user-script SMF source-hash field.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
