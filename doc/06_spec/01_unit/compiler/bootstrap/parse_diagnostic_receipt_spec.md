# Parser diagnostic receipts

Source-authored companion for
`test/01_unit/compiler/bootstrap/parse_diagnostic_receipt_spec.spl`.
SSpec execution and native lifetime verification: UNRUN.

| Scenario | Expected result |
| --- | --- |
| Suppressed parser output | Driver message contains the malformed file path and actual first parser error |
| Bad / good / different bad | Ordinary good parse clears the first receipt; subsequent bad input reports its own different reason |
| Retained text | A captured diagnostic remains unchanged after another module replaces parser state |
| Error flag without receipt | Message explicitly identifies missing diagnostic evidence rather than referring to stdout |
| Cold and warm cache boundary | Failed cold parse publishes no cache blob; a valid flat-pool cache hit clears previous first-error text; subsequent malformed input reports its own error |

The cache case uses the real in-memory flat-pool capture/restore entrypoints.
It does not claim disk/CAS cache transport coverage. These checks retain failure
verdicts; they do not treat missing diagnostic text as successful parsing.

The uncapped full CLI's 130 reported paths remain unclassified. The separate
direct `modes.spl` probe passed parse, HIR, MIR, and object generation on the
original producer, then failed runtime linking. See
`doc/08_tracking/bug/uncapped_full_cli_parser_diagnostics_2026-10-02.md` for
identities, both earlier cap failures, and the three-cycle stop condition.
