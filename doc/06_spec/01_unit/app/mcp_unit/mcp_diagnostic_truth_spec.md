# MCP diagnostic truth manual

Status: authored manual, not generated PASS. Executable: test/01_unit/app/mcp_unit/mcp_diagnostic_truth_spec.spl.

1. Parse a Windows-drive warning and a colon-containing POSIX-path error; preserve line, column, severity and message.
2. Reject a nonnumeric column or a word that merely begins with a severity name.
3. Render a warning despite successful analyzer exit.
4. Preserve timeout status alongside already-emitted diagnostic text.
5. Classify crashes, launch failures and failed analyzers without findings as analysis failure.
6. Retain producer failure in summaries even when partial findings exist.
7. Keep absent or arbitrary successful text output unverified instead of reporting clean.

VIEW-15 empty-file behavior uses file_read_result in the real handler; public MCP empty/missing-file acceptance is still pending. DIAG-01/02/03 focused regression execution is blocked before test bodies by the available non-admitted binary's bounded_bytes.spl parse error. No runtime PASS or coverage percentage is claimed.
