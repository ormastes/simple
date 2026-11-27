# Literal byte and explicit paste source candidate

Status: **WARN / NOT_RUN**, source cycle 1. Twelve pure cases and three native scenarios authored; zero executed. Child fixture NOT_BUILT. Independent source review pending. No build, compiler, native/helper/product execution, staging or commit was performed.

Approved scope: four public Sys/native/SOSIX facades, input_queue, pane_io_service, new paste-only core_mux_input_codec and explicit-state core_mux_input_service, focused specs/manuals/fixture/plan. Root API, active L1 context, configured-launch owner, VT modes, key codec, common contracts and native PTY owner bodies are untouched.

## Mechanism and authority

The default Sys provider explicitly reports literal-byte support false and returns Err from write_literal_some_v1 without calling its legacy UTF8-to-text writer. The selected Windows facade reports the installed exact-channel mechanism and delegates to the existing bounded overlapped byte writer. No new extern, native buffer owner or ABI is introduced. Both configured SOSIX families forward the same two symbols. Availability is not live startup proof, native qualification or child-delivery evidence.

PaneInput adds a default-false literal_pty marker so existing constructors remain compatible. Exact byte enqueue preserves every octet, retained offset and sticky error; it never decodes, re-encodes or logs the payload. All retained bytes—including consumed prefix—count against 65536. Existing text/reply enqueue uses checked canonical byte extraction and preserves the marker after literal input. Original text is discarded once it cannot represent the stream; a marked queue cannot use the piped text ABI. Complete drain resets the marker, while partial advance/failure preserves it. Joined byte and legacy text allocation failures refuse rather than dropping content.

The effect path uses the same pure scoped admission helper as tests, validating actual session/window/pane ancestry, closing state, retained child/PTY identity and explicit support before host work. Queue capacity is reserved before the actual live-child query. A positive stored PID alone is not treated as current Running evidence: the selected child owner is queried before enqueue publication/write. The bounded flush checks native pending state and writes at most4096 bytes. Immediate/async acceptance advances only the transferred byte count; errors preserve exact returned state with commit=true after queue/native effects. Closing paths do not flush. No full-request replay is introduced.

The provider's accepted count may mean bytes copied into its retained overlapped buffer; input_pending/idle distinguishes completion but never proves child consumption. The native owner still retains pending buffers and failed cleanup authority. L2/global cleanup contracts are unchanged.

Paste honors its explicit bracketed and append_enter flags: optional start marker, exact byte body, optional end marker, optional CR. It checks complete overhead and arithmetic, allocates one bounded result, and submits one atomic queue admission. It does not infer brackets from VT state or convert a byte body to text. Capacity refusal does not send an orphan marker or prefix. Public common validation remains the adapter's responsibility before mapping; the helper cannot qualify a full endpoint.

## Evidence and honest limits

Pure controls call actual production queue, codec and admission functions. Synthetic PID/fd values never enter native paths. Native authored controls use an actual separately compiled console child with unchanged configured launch, retain all returned states and clean before assertions. The Unicode child emits a computed marker only after exact supported input observation and console restoration. The invalid-byte case observes real channel acceptance/completion only, not fabricated child stdin identity.

[Microsoft's pseudoconsole contract](https://learn.microsoft.com/en-us/windows/console/pseudoconsoles) describes UTF8 channel interpretation and internal translation. POSIX terminal discipline can also transform input. Thus exact smux queue/WriteFile bytes and downstream child effects are distinct. No unsupported fallback or hidden UTF8 replacement is used to manufacture a passing child-byte test.

The approved test-only app.io env facade obtains the fixture path; no raw environment extern or cross-family alias is added. Native failure injection, real backpressure saturation/fairness, generic negative-profile execution, resource measurements, actual binary/runtime lineage and all execution remain pending. Compiled SSpec/docgen/maintenance and core/lib/MCP smoke gates are not claimed completed.

Full SendKeys is incomplete: DECCKM state and scalar modifier/F13–F24 policy are separate approved-design gates, not implemented here. Root still owns API extraction/hooks, atomic publication, common receipts and server capability admission. This explicit-state slice is not a connected or fully admitted CoreMux provider.

## Source correction cycle 2

Independent review identified P2-L3-01: the channel native scenario queried input status without running the owner pump, so legitimate pending/zero initial acceptance could leave queued bytes stalled even though normal service polling would progress. The v1 source manifest and independent report retain that historical finding and all original pins.

The channel observation branch now calls production `pane_poll_state(state, [], [])`, retains its returned state, then queries and retains `pane_input_status_state`. The fixture owns exactly one nonclosing pane in its explicit state. The existing bounded owner poll drains at most eight chunks for that pane and flushes through the real pending/byte-write path. No direct writer bypass, forced advancement, mock completion, retry of the entire input request or child-byte fidelity assertion was added. Existing attempt/deadline bounds and cleanup-before-assertions remain.

Only the system spec, its manual and this author report changed in this correction. Production, pure cases, child fixture and plan are unchanged. Twelve pure and three native cases remain authored, zero executed; the fixture remains NOT_BUILT. V2 independent review is pending. No compiler/build/test/native/helper/product execution, staging or commit occurred.
