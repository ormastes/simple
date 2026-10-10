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

## Nongeneric SMTP and I/O continuation (2026-10-10)

Producer `4cca9585` on source `6320be383` clears the earlier I/O facade
`thread_sleep_ms` HIR failure after binding the canonical millisecond thread
owner. That owner imports no modules, so the alias adds no import cycle.
The CS fixture still fails MIR (exit 1, no object) on `then`, `is_open`,
`close`, and `trim` owners; it is not qualified. Receipt:
`/home/ormastes/simple-phase4-web-a0-parallel-20261010/leaf-fixtures/cs-host-alias-sleep-epoch02/evidence.json`.

The earlier SMTP fixture identifies unsupported `append` calls in three
configured send owners and an absent numeric `to_hex` method. Use the existing
array `push` API with explicit text arrays and the common uppercase formatter.
Quoted-printable characters now retain two hexadecimal digits for a control
byte (tab is `=09`). The fixture checks exact message bodies for all three
owners and both ordinary/control quoted-printable bytes, in addition to the
existing recipient checks. Native verification is pending; no compiler generic
repair or configured-family routing change is included.

Focused SMTP verification: epoch02 removed all array append diagnostics, then
exposed the same numeric formatting calls in the async utility owner. Apply
the common formatter to all three physical family copies. Epoch03 compiled
a 364808-byte object (exit 0), linked (exit 0), and executed all nine native
checks (exit 0; exact `smtp-recipient-arrays-ok` stdout). Receipt:
`/home/ormastes/simple-phase4-web-a0-parallel-20261010/leaf-fixtures/smtp-api-epoch03/evidence.json`.
This is focused provisional LLVM evidence, not a full application or release
qualification; producer remains unadmitted.
