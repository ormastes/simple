# MCP reader diagnostic truth

Owner: release100 mcp_lsp_audit; status: claimed, runtime verification pending.

Baseline e2ce7042552. main_lazy_diag_tools.spl:153 rejects valid empty reads; :177 suppresses warnings on successful analyzer exit; :49 parses first three colons and therefore rejects Windows paths. The JSON formatter duplicates that defect. Diagnostic summary can claim no diagnostics after producer failure.

Reproduce: parse_diag_text_line("C:/work/test.spl:10:5: warning: unused") returns empty; successful check output containing a warning is suppressed by the read/edit branches. Pure-Simple owner delegates file reading and subprocess invocation correctly; repair the app formatter/read boundary, no runtime change needed.

Exact and adjacent regression: Windows drive path and colon-containing POSIX path; success warning and failed analyzer; empty and missing file read. Completion requires executable focused regressions and public MCP smoke on admitted runtime.

## Repair and evidence

Source repair authored in the pure app owner. Shared colon locator fixes both formatters; file_read_result retains valid empty reads; read/edit/multi-edit expose warning and producer status through shared diagnostic_check_status/details. Full DiagnosticV1 normalization remains open.

Pre-fix reproduction attempt: deployed /Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple test test/01_unit/app/mcp_unit/mcp_diagnostic_truth_spec.spl --mode=interpreter, bounded to 30 seconds. Exit 1 before test bodies: bounded_bytes.spl parse error (expected expression, found Colon). Log /private/tmp/mcp-diagnostic-truth-before.log. This binary was subsequently identified as non-admitted and its output is diagnostic-only. No retry or runtime PASS. Source inspection independently establishes the defective branches; behavioral reproduction and repaired assertions await admitted Stage4. Owner: root integration; unblock: admitted Stage4 binary and focused/public-interface execution.
