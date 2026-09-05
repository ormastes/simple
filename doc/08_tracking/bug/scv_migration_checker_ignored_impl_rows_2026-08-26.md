# SCV migration checker structurally ignored SCV-IMPL ledger rows (2026-08-26, FIXED same day)

**Found by:** W4 + Wave-1 closeout lane, while flipping the 8 Wave-1 rows.

**Symptom:** `sh scripts/check/check-scv-migration-todo.shs --now 2026-09-29T12:00:00Z`
reported `PASS — 0 step(s) due, nothing to do (25 done, 0 pending)` while the
ledger `.spipe/scv-migration/todo.sdn` held 8 due, pending `SCV-IMPL-*` rows.
Silent skip, green verdict — the same vacuous-pass class as the lane-B
doctor gap.

**Root cause:** two hardcoded id shapes in the signed checker:
- row match: `case "    SCV-MIG-"*` — any other id fell through to the
  copy-through branch and was never counted, so `total` excluded IMPL rows
  and the quiet-hour verdict was computed over MIG rows only;
- step-path extraction: `grep -o '...SCV-MIG-[0-9][0-9]*\.shs'` — an IMPL
  check_cmd would have classified as `bad_check_cmd` even if matched.

**Fix (this landing):** row match extended with `"    SCV-IMPL-"*`; step grep
widened to `SCV-\(MIG-[0-9]*\|IMPL-[A-Z]-[0-9]*\)\.shs`; new fatal selftest
fixture F7 pins the extension (signed IMPL step -> done); fixture count
6 -> 7 everywhere it is stated. Checker re-signed with the scv-migration-root
WOTS key (leaf 40) and re-verified against
`config/trust/scv_migration_root.pub`.

**Defect-class note:** a fail-closed checker with a fail-open ROW FILTER is
still fail-open for anything the filter does not name. Any future id family
added to the ledger must ship with a matching selftest fixture.
