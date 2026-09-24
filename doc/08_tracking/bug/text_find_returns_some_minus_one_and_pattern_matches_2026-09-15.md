# `text.find(needle)` returns `Some(-1)` when absent and treats needle as a pattern
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- **Observed (2026-09-15, seed `bin/release/aarch64-unknown-linux-gnu/simple`):**
  `text.find(needle)` on a missing needle returns `Some(-1)` instead of
  `None`, and the needle is treated as a pattern — so `"?"` (or other pattern
  metacharacters) always matches. Found while fixing
  `test/01_unit/app/tooling/url_utils_spec.spl` during the 2026-09-15 test wave;
  the spec's URL/query parsing was rewritten on `index_of` as the workaround
  (spec-local only, lib untouched).
- **Impact:** any caller doing `s.find(x).? >= 0`-style membership or using
  `find` with user-controlled needles gets wrong answers silently.
- **Expectation:** absent needle → `None`; literal substring semantics or a
  clearly separate pattern API.
- **Unblock condition:** `text.find` returns `None` on miss and does literal
  matching (or a documented `find_pattern` split); add a std spec asserting
  both.

