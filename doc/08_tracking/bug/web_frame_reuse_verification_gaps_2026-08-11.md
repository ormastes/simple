# Web frame-reuse verification gaps

## Status

Open. Revision-only IPC is implemented but cannot yet be promoted as verified
8K frame-switch evidence.

## Protocol result

`browser_renderer_frame_reuse_protocol_spec.spl` originally failed semantic
analysis because the protocol used nonexistent `text.byte_at`. The decoder now
converts text to bytes once per operation, avoiding both that error and an
O(n^2) repeated-conversion workaround. The suite reaches assertions and reports
1 pass / 1 fail, but the current runner emits no failing assertion detail and
ignores `SIMPLE_TEST_FILTER`; the exact remaining expectation is unresolved.

## Broker result

`hosted_browser_frame_wire_receipt_spec.spl` reports a parser error in
`hosted_browser_renderer_process.spl`: `expected identifier, found LParen`,
without a line number. The newly added receipt accessor uses canonical `me`
method syntax. A bounded direct `check` did not converge, so further blind
syntax changes were stopped.

## Required resolution

Restore assertion diagnostics and honored filtering in the admitted runner,
make parser errors include source locations, then prove: full frame retained;
matching revision-only reply accepted; stale/missing revision rejected; exact
full/reuse IPC bytes counted; unchanged frame sends no DrawIR/images. These are
mechanism receipts only—8K/80 additionally requires the campaign matrix row.
