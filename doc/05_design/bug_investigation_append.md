# Bug investigation append detail and evidence

Implementation: src/lib/nogc_sync_mut/database/bug.spl and src/lib/nogc_async_mut/database/bug.spl, method add_investigation_log(id: text, content: text) -> bool.

Validation order: known bug; nonempty codec-safe content; exact canonical log columns; valid unique target line numbers; idempotency; one append. A line number at the portable parser maximum is rejected because no parseable successor exists. Line gaps and interleaved other-bug rows are preserved.

Tests: test/02_integration/lib/database/bug_investigation_append_spec.spl and bug_investigation_append_async_spec.spl. They intentionally import real profile owners rather than the local fake SdnDatabase still present in database_core_spec. Each profile uses a separate scratch path. Helpers: fixture, table_text, check_unchanged. Every scenario uses production operations and concrete row/content/CRC assertions.

REQ-BUG-NOTE-001: first append, sparse append, missing legacy table; preservation of custom main columns, description/strategy and unknown evidence table; Unicode/comma round-trip. REQ-BUG-NOTE-002: repeat before/after reload and cross-bug content independence. REQ-BUG-NOTE-003: unknown bug, unsupported text, malformed/negative/overflow/duplicate numbering, extra columns.

Verification state: source and fixture inspection only until a qualified self-hosted runtime executes the specs. No coverage percentage, generated-manual quality, full library/compiler check, native smoke or overall PASS is claimed. Root coordinates independent review and integration. This repair alone does not qualify bug_resolve because its token accounting owner methods are separately missing.
