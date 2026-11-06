# Std text codec validates UTF-8 with an interpreted per-byte loop

- **Filed:** 2026-11-06 (libbug coordinator, from the traceability lane, PR #7197)
- **Status:** open (P2 perf)
- **Symptom:** reading `doc/08_tracking/bug/bug_db.sdn` (3.67 MB) through
  `read_file_text_result` / `file_read_regular_no_follow_bounded` takes ~21 s on the seed;
  the same bytes via `string_from_byte_array` + `text_validate_utf8` take 0.28 s (~75x).
- **Cause:** the std text codec's UTF-8 validation is a per-byte interpreted loop instead
  of the native `text_validate_utf8` path.
- **Fix direction:** route the codec's validation through `text_validate_utf8` (or the
  runtime's bulk validator) and keep the per-byte loop only as the reference twin.
- **Repro:** time `read_file_text_result("doc/08_tracking/bug/bug_db.sdn")` on the seed.
