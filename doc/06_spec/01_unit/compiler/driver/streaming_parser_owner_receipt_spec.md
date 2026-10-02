# Streaming parser boundary regression

Fixture: `test/fixtures/streaming_parser_ownership/main.spl`.
Spec: `test/01_unit/compiler/driver/streaming_parser_owner_receipt_spec.spl`.
Native/SSpec status: **UNRUN**. Default streaming remains unchanged.

Compile the fixture with a pinned native producer and record its binary hash,
producer source, fixture source and runtime identities. Set
`SIMPLE_STREAM_PRODUCER_SHA256`, `SIMPLE_STREAM_PRODUCER_SOURCE_REVISION` and
`SIMPLE_STREAM_SOURCE_REVISION` to the independent receipt values. Run fresh
processes as `<fixture> surface <absolute-fresh-root>` and
`<fixture> hir <different-absolute-fresh-root>`, under the same external 7 GB
guard. Save stdout as `surface.env` and `hir.env`; bind their directory through
`SIMPLE_STREAM_REPORT_DIR` for the admitted SSpec runner. Missing reports fail.
Do not use a seed as a general runner or treat echoed identities as admission.

Both modes start before any parser initialization and require an unavailable
required provider to fail without entering the parser. The HIR mode catches
the old implicit Reference fallback. After selecting Reference, the first cold
parse occurs inside the tested production scope. A malformed module follows;
two later valid modules must still parse, preserving the earlier error text
and diagnostics. The surface mode checks resource/unsafe/open-enum metadata
after each close and preserves the first callable in the builder. The HIR mode
re-encodes the first retained complete HIR after the later scopes and requires
the same nonempty digest. Successful module and parser initialization counts
are exact, not inferred from a no-error log.

This is a focused boundary regression. It deliberately reports
`collector_active=no`: reverse-reference phase publication currently has a
separate ownership gap. Shared-cache identity transitions remain covered by
the queued ordinary-parser fixture and need a full-route parity run before
general enablement. Direct fault injection for registry finalization errors
also remains pending. Passing this fixture cannot qualify all streaming
features, full inventory, coverage/MC/DC, VHDL, or full builds below 7 GB.
