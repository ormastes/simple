# Bug: lint COLL006 "string concat in loop" fires on concat-free fns and misses a real concat loop

- **Date:** 2026-07-27
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** medium (noise + missed real finding)
- **Found by:** SimpleOS harden lane P7 (config_core)

## Symptom
- False positive: a 7-line function containing only an i64 counter loop (zero
  string operations) reports 2 × COLL006 "string concat in loop".
- False negative: the genuine concat-in-loop in
  `src/lib/common/config_core/config_int_to_text` is NOT reported.
- Reproduces on untouched `src/lib/editor/00.common/*.spl` sources too —
  pre-existing, not introduced by the config_core extraction.

## Next step
Re-derive COLL006's loop-body expression walk: it appears to match on
loop-variable reuse rather than actual `text + text` in a loop. Add fixtures
for both directions (concat-free loop must not fire; accumulating concat must).
