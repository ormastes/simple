# Bootstrap preflight PASS was neither retained nor bound to resumed phases

Status: FIXED
Area: bootstrap / admission evidence
Severity: P0 false acceptance

## Defect

`check-bootstrap-preflight.shs` printed an advisory PASS, but the canonical
bootstrap entrypoint did not run it, retain its result, or bind it to source,
Git HEAD, seed bytes, checker bytes, and selected bootstrap configuration.
Stage 3 and Stage 4 continuation receipts therefore could not prove that their
lineage had passed preflight. A stale terminal transcript could be mistaken for
current evidence.

## Fix

Full bootstrap runs now execute the checker while holding output ownership and
publish `bootstrap-preflight.env` only after the source and Git snapshots are
identical before and after all checks. The receipt records exact source, Git,
configuration, seed, and checker hashes. Receipt verification rejects missing,
symlinked, duplicate-key, stale, malformed, or cargo-skipped evidence.

Stage 3 and Stage 4 resume paths verify the receipt against the current tree
before compilation and copy its canonical path and SHA-256 into their own
status or continuation receipt.

## Regression

`test/01_unit/scripts/bootstrap_preflight_evidence_contract_test.shs` proves a
structurally plausible cargo-skipped PASS cannot be admitted, checks that the
producer runs after lock acquisition and before any stage starts, and checks
that both resume lanes verify and preserve preflight provenance.

Focused result on macOS: `bootstrap_preflight_evidence_contract=true`.
