# Raw SFFI unsafe ratchet extracts zero rows after inventory schema drift

- **Status:** EXTRACTOR FIXED; GLOBAL BASELINE DRIFT OPEN
- **Filed:** 2026-08-26
- **Area:** SFFI static verification tooling
- **Severity:** high — the global unsafe-declaration debt ratchet cannot provide
  trustworthy pass/fail evidence

## Evidence

Running `sh scripts/check/check-raw-sffi-unsafe-ratchet.shs` once on the current
tree produced an inventory summary with 13,025 declarations and 9,503
`unsafe_tag_and_contract_missing` rows, but its `extract_missing` stage reported
`current=0`. It consequently classified all 12,766 frozen baseline identities
as stale and failed.

The ratchet currently selects rows with `awk ... $7 == "missing"`. The
inventory output/schema has evolved, so that positional predicate no longer
selects the missing-unsafe state. Regenerating the baseline would erase real
debt and is not an acceptable workaround.

## Required fix

Version the inventory TSV schema or resolve columns by header name. Add a
self-test that feeds the current production schema and proves at least one
tagged and one untagged declaration are distinguished. Only then regenerate or
review baseline deltas. Until repaired, the focused family ratchets and direct
inventory statistics are evidence; the global unsafe ratchet is blocked.

## Source fix

The extractor now uses the current v2 positions: symbol `$1`, source signature
`$5`, file `$6`, and unsafe tag `$8`. The frozen baseline remains intact except
for explicitly reviewed declarations that became tagged; it was not
regenerated.

The one post-fix recheck successfully extracted 9,858 untagged identities and
then truthfully failed on separate repository-wide drift: 542 new identities
and 3,450 stale identities. Those rows span unrelated concurrent owners and
must be reviewed rather than bulk-accepted or deleted. The extractor defect is
fixed; the global ratchet remains red for real baseline ownership work.
