# MCI-v2 docgen provenance receipt is not emitted

## Status

IMPLEMENTED, NOT RELEASE-VERIFIED — still blocks MCI-DOC-001 and MCI-DOC-002.

## Evidence

The traceability producer requires
`doc/06_spec/03_system/infra/mission_critical_infra_hardening_v2_spec.docgen-receipt.env`
with schema `mci-spipe-docgen-provenance-v2`. The canonical owner now accepts
`--provenance-receipt`, binds the canonical executing binary, source, generated
manual, command, version, and run identity, then publishes atomically only
after successful zero-stub generation. The focused shell contract constructs a
synthetic receipt fixture; that proves validation only and is not release
evidence.

The deployed `bin/simple` currently prints the Rust bootstrap-seed warning, so
it is independently inadmissible for release docgen.

## Required fix

Verify the versioned docgen-owned provenance output, which atomically binds:

- the exact admitted self-hosted binary path and SHA-256;
- tool/version identity and canonical logical command;
- executable SSpec path and SHA-256;
- generated manual path and SHA-256;
- generation timestamp/run identity and successful exit;
- no-stub/manual-quality verdicts required by the SPipe contract.

The traceability producer must snapshot and validate those exact fields. A
hand-authored receipt, placeholder binary path, Rust seed, or manual hash-only
fixture must fail closed.

## Resume

Run the focused receipt and traceability contracts, rebuild/admit an
exact-current pure-Simple CLI, run docgen once with `--provenance-receipt`,
then run
`test/01_unit/scripts/mci_v2_traceability_contract_test.shs` and the live
traceability producer.
