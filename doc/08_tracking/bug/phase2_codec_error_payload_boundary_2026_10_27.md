# Pinned Phase 2 codec error payload mismatch at the I/O enum boundary (2026-10-27)

Canonical bug ID: `phase2_codec_error_payload_boundary_2026_10_27`

Canonical bug database registration: **PENDING**. Do not treat this identifier
as an admitted database row until the canonical bug writer records it.

## Evidence

The pinned standalone API probe passed HIR import resolution, then failed MIR
lowering in
`D:/dev/simple-object-repairs-luna-20261027/build/object-repair/file-size-api/run-entry/compiler.log`.
After the indexed-loop workaround, the follow-up
`D:/dev/simple-object-repairs-luna-20261027/build/object-repair/file-size-api/shared-io-run/compiler.log`
no longer reports the `file_text_session.spl` array-loop errors, but reports
two payload type mismatches constructing
`lib.nogc_sync_mut.io.external_text_io.TextIoError.Codec`. A final bounded
callsite-boundary attempt at
`D:/dev/simple-object-repairs-luna-20261027/build/object-repair/file-size-api/shared-io-final-call-boundary-run/compiler.log`
reached HIR but still reported one codec payload mismatch. No executable was
produced and no runtime result is available.

Callsite review of the retained closure identified direct constructors in
`file_text_session.spl` and `file_external_compat.spl`. `CodecError` has one
source declaration in `src/lib/common/encoding/external_text.spl`. The
diagnostics and source shape do not prove the responsible MIR owner.

## Attempt history

Four actual stages were recorded against the unchanged pinned producer:

- Baseline API probe (`file-size-api/run-entry/compiler.log`): original
  constructors and byte loops produced two codec payload mismatches, alongside
  the two array-loop diagnostics.
- Typed helper plus indexed loops (`file-size-api/shared-io-run/compiler.log`):
  two codec mismatches remained and the array-loop diagnostics disappeared.
  The standalone fixture changed during compilation; this run is diagnostic
  evidence only and does not qualify either fixture version for runtime use.
- Explicit payload imports, without typed Result locals
  (`file-size-api/shared-io-visible-type-run/compiler.log`): one codec mismatch
  remained. The corrected standalone fixture stayed frozen.
- Imports plus typed Result locals at both consumer callsites
  (`file-size-api/shared-io-final-call-boundary-run/compiler.log`): the same
  single codec mismatch remained. No executable or runtime PASS was produced.

All codec helper, import, and Result-local candidates were reverted. Only the
separately tagged indexed byte-loop change remains outside this codec repair.

No codec workaround remains in source. The exact compiler cause is unresolved;
the immutable pinned producer was not rebuilt. Canonical bug database
registration remains pending.

## Existing semantic coverage

`test/01_unit/lib/nogc_sync_mut/io/external_text_io_payload_spec.spl` compares
real decoder failures and asserts `kind`, `byte_offset`, and `reason` on the
wrapped payload. `test/02_integration/io/external_text_io_spec.spl` covers
unknown encoding and malformed UTF-8 payloads; file-session integration tests
cover malformed UTF-8 and BOM policy errors. These existing cases are retained,
not replaced with source-text checks.

## Qualification status

The pinned producer reached HIR but failed MIR and produced no object for the API
probe. Runtime payload behavior is unqualified. Source review and existing test
assertions are not native/runtime PASS evidence. Canonical bug database
registration for this ID remains pending.
