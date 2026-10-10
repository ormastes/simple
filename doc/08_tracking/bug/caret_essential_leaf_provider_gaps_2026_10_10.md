# Caret essential leaf provider gaps

Status: OPEN; source repair and regressions AUTHORED_UNEXECUTED.

Actual aa404/a0 Caret closure HIR errors: helpers_compat imports absent std.io.file_read; tui_io calls unbound print_raw; pane_team imports three functions not declared by multi_caret_manager. Retained evidence: /home/ormastes/simple-phase4-web-a0-parallel-20261010/caret/build/failure-summary.json. This is a source provider repair, not permission to suppress diagnostics.

The MCP leaf now uses the existing SoSix file-read alias. The SoSix facade adds a signature-identical print_raw alias to the canonical sync diagnostic owner; Caret emits through that alias. File-read empty/missing semantics remain unchanged. Manager snapshot adapters expose existing constructor/poll/stop rules without spawning, polling or killing processes; the process-owned functions delegate to the same rules.

Regression scenarios exercise exact UTF8 file content, partial/all-live/all-dead snapshots, terminal no-ops, teardown leak ownership and empty teams. The native fixture requires exact stdout alphaé|β| with no added newline and exit0. None has executed yet.

Platform source review: file_ops and diagnostic owners are reused, not replaced by a shell or app runtime extern. Linux runtime qualification is pending; Windows, macOS, FreeBSD and SimpleOS execution is unverified. Existing unavailable backend contracts remain authoritative.
