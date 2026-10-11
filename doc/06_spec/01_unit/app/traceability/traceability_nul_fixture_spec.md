# Validate binary-framed capture fixtures

Authored companion to test/01_unit/app/traceability/traceability_nul_fixture_spec.spl.
Actual native evidence: three examples, zero failures. Full qualification remains open.

1. Extract successful UTF8 Result payload and assert exactly one NUL byte.
2. Decode real NUL framing with Unicode/newline and marker-like filename text.
3. Preserve adjacent Unicode records; reject empty and unterminated records.

The original capped suite6/1 is preserved; no fixture-dependent assertion is
retroactively validated. Use explicit Result matching, rather than nil coalescing,
to create the fixture. See doc/09_report/traceability_cli_tdd_2026-10-11.md.
