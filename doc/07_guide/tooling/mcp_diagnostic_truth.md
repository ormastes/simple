# MCP compatibility diagnostic truth

The legacy `simple_read` contract still returns numbered source and runs the existing bounded check. The separate source-view route owns folded projections and sessions; this compatibility path does not claim those features.

Reads use `file_read_result`, so an empty file is readable and missing/failed reads remain errors. Text compatibility diagnostics locate numeric line/column fields after path prefixes, including Windows drive letters and colon-containing paths. The text and JSON formatters share location detection.

Read, edit and multi-edit results retain diagnostics even when the check exits successfully. Timeout, producer failure, missing output, and unverified text completeness are distinct from findings. A successful exit with no parsed diagnostics is not proof of a clean canonical DiagnosticV1 analysis. The compatibility formatter still does not preserve multiline labels or macro provenance; the planned structured diagnostic store must supply those.

Runtime admission is pending: the installed v1.0.0-beta binary is not admitted Stage4 and fails before the new regressions in bounded_bytes.spl. Do not advertise this source repair as deployed behavior until an admitted MCP binary and public-interface smoke pass.
