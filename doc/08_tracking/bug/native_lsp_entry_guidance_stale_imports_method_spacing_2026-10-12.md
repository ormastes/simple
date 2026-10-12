# Native LSP entry does not serve the protocol

Status: source repair authored; native execution and bug database registration
pending. No compiler or fixture process was started for this repair.

Observed from the actual source of the frozen canonical attempt12: the CLI's
`cli_run_lsp` selects `src/app/lsp/main.spl`. Its default `main` unconditionally
prints compiled-mode guidance and returns1, even when that file is compiled.
Help/version success therefore cannot qualify native LSP startup.

The genuine loop in `src/lib/nogc_sync_mut/lsp/main.spl` uses stale
`app.lsp.lsp_json`, protocol and handler imports; that app directory contains
only the guidance entry. Its exact compact-substring method dispatch also
rejects valid ordinary JSON spaces after a colon. The fast query child path
names a nonexistent app file rather than the actual std query implementation.

Repair: the app calls the real exported loop after unchanged help/version
checks, and debug startup uses stderr. The std entry retains direct executable
behavior through an explicit main and imports actual std protocol modules.
Dispatch parses the top-level method once with the existing strict typed JSON
parser, accepting ordinary whitespace and ignoring misleading params.method.
Actual handler/protocol helper dependencies are declared. The query path is
corrected, and file URIs decode UTF-8 percent escapes plus standard drive URI
spelling before reaching the shared filesystem boundary.

Query children now use the existing bounded process API with a typed argv
array and the original 30/60 second limits. Decoded spaces, UTF-8 names and
shell punctuation remain individual arguments, including a binary path with
spaces. An exact current-workspace path is expressed in the existing relative
query surface; the query visibility sanitizer is unchanged. Debug stderr
records the actual child binary, JSON argv and returned status.

The compiled-tool protocol fixture sends ordinary pretty JSON, a UTF-8
document name/text with a space-bearing filename, initialize, a genuine document-symbol query, an unknown
UTF-8 method with nested params.method, shutdown and exit. Its verifier reads
raw byte frames, decodes strict JSON, checks exact numeric/string ids,
capabilities, function kind/source line, exact error code/message and null
shutdown result. It rejects empty, truncated, unframed, duplicate-id and
unsuccessful/unenforced process evidence. All controls are UNRUN.

The MCP and LSP-MCP transcripts are separate service controls. They do not
replace native editor LSP. Normal runtime/tool/source authority and compiler
admission remain mandatory; no Rust seed or source stub delegation is a pass.
