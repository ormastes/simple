# Sanitizer Waiver Ledger (cert C4)

Waiver ledger for `scripts/check/cert/sanitizer-matrix.shs`
(spec: `doc/03_plan/cert/sanitizer_matrix_plan.md`).

Every sanitizer finding is filed the day it is observed and triaged within a
2-business-day SLA as: (a) real defect -> fix, (b) false positive / known
sanitizer limitation (e.g. MSan + uninstrumented libc FFI) -> waiver here, or
(c) needs investigation -> stays open.

Rules:
- One row per waiver, scoped to a **specific finding signature** (stack hash or
  `file:line` + call context) — never a path-level or sanitizer-level opt-out.
- **No blanket suppressions** (no repo-wide `.asanignore` over a directory).
- Expiry = grant date + 90 days. An expired waiver is stale: the next run must
  re-triage (fixed -> remove the row; still valid -> renew with a fresh
  justification and new 90-day expiry) or the finding is treated as a regression
  that fails the gate. `--full` runs enforce expiry.

The `expiry` column MUST be `YYYY-MM-DD`; the harness parses it to count active
vs. expired waivers.

| finding | sanitizer | file:line | justification | granted | expiry | owner |
|---|---|---|---|---|---|---|

<!-- No active waivers. All sanitizer cells are currently PASS or toolchain/
platform-gated SKIP; nothing has been waived. -->
