# Caret essential leaf provider gaps

Status: OPEN; source repair and regressions AUTHORED_UNEXECUTED.

Actual aa404/a0 Caret closure HIR errors: helpers_compat imports absent std.io.file_read; tui_io calls unbound print_raw; pane_team imports three functions not declared by multi_caret_manager. Retained evidence: /home/ormastes/simple-phase4-web-a0-parallel-20261010/caret/build/failure-summary.json. This is a source provider repair, not permission to suppress diagnostics.

The MCP leaf now uses the existing SoSix file-read alias. The SoSix facade adds a signature-identical print_raw alias to the canonical sync diagnostic owner; Caret emits through that alias. File-read empty/missing semantics remain unchanged. Manager snapshot adapters expose existing constructor/poll/stop rules without spawning, polling or killing processes; the process-owned functions delegate to the same rules.

Regression scenarios exercise exact UTF8 file content, partial/all-live/all-dead snapshots, terminal no-ops, teardown leak ownership and empty teams. The native fixture requires exact stdout alphaé|β| with no added newline and exit0. None has executed yet.

Platform source review: file_ops and diagnostic owners are reused, not replaced by a shell or app runtime extern. Linux runtime qualification is pending; Windows, macOS, FreeBSD and SimpleOS execution is unverified. Existing unavailable backend contracts remain authoritative.

## Restart collection: concrete leaf type gaps

The aff317 producer on source dce92 reached a real 323-module Caret HIR
closure after SCV ownership was restored. The closure still failed (exit 1,
241.67 seconds, 62 diagnostic records in 14 files); no Caret binary or runtime
qualification is claimed. Earlier missing file/terminal providers and pane
manager adapters no longer occur in this diagnostic set.

Two additional leaf defects are repaired: `main.spl` used `ModelProfileV1`
without importing that existing canonical type, and all three SMTP configured
implementation families declared an undefined `List` return type despite
returning an array of text recipients. The repair imports the type and changes
only those three return annotations to `[text]`; routing and function bodies
remain intact. Owned source references contain only the three declarations.

Reproduction: the failed closure reported two `unresolved type: ModelProfileV1`
records and two `unresolved type: List` records. Prevention:
`test/01_unit/lib/smtp/recipient_array_type_spec.spl` has three scenarios and six
real array assertions, including whitespace/empty input and all three configured
families. `test/fixtures/lib/smtp_recipient_array_type/main.spl` supplies four
executable typed checks. Both are AUTHORED_UNEXECUTED; compiler source, backend,
runtime, cache, and execution receipts must be bound before qualification.
Remaining enum payload, local binding, and collection method failures remain
open. No host access or runtime FFI declaration changed.

Concrete leaf type repair commit: `e298d4513` (qualified tests still pending).
