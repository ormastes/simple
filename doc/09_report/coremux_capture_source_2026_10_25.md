# CoreMux capture source handoff

Status: **WARN / NOT_RUN**. Source implementation and authored scenarios only.
No compiler, native product, helper, SSpec, SPipe, or build was launched. No
commit was made. Existing unrelated work was preserved.

## Source boundary

Owned changes are `src/os/apps/smux/service.spl`, `pane_io_service.spl`,
`vt_screen.spl`, and new `vt_types.spl`, `vt_capture_state.spl`, `vt_capture.spl`,
`capture_cursor.spl`, `vt_retention.spl` and `vt_snapshot.spl`. Frozen common
CoreMux contracts were not changed. The API,
server, remote protocol, presentation/frame owner and native provider are other
lanes. `vt_screen` re-exports its existing `VtScreen` entry point after type
extraction; no helper imports the parser back from its value-types module.

## Owner integration

`PaneRecord` now carries `content_revision`, `ingestion_sequence`, and
`child_incarnation`, all u64, plus `tail_truncated`. Every value constructor
preserves them. New child
attachment or retained failed-spawn reservation increments incarnation; close
and retries preserve it. `can_attach()` must run before host launch effects and
rejects incarnation/content exhaustion. New resize paths must likewise reject
content exhaustion before host resize effects. `can_ingest()` reserves 1 MiB of
counter space before each native read. Source inspection confirms the pipe
decoder ceiling is 24,585 UTF-8 bytes; the Windows PTY author confirmed its 8,192
raw-byte read and at most three-byte retained UTF-8 tail also fit this reserve.
Those are source bounds, not measurements. The ingestion counter counts UTF-8
bytes delivered by the provider's decoded text read, including replacement
text. It does not measure raw syscall bytes. The provider can consume an
incomplete UTF-8 fragment while returning empty text, so an unchanged counter
alone does not prove zero native-byte consumption.

`PanePidUpdate.cleanup_pending` is explicit. Failed spawn plus failed/deferred
close retains the exact fd and old screen with `commit=true`, `cleanup_pending=true`
and an error. Subsequent spawn rejects a retained fd. No-child cleanup owners
cannot flush input or drain output. The API must publish failure-side state and
map cleanup status into the request receipt.

`capture_cursor_apply(owner, lease, pane_ref, record, request, observed_revision,
ingestion, now_ms)` returns `CaptureCursorUpdate(owner, result)`, with typed
`CaptureFailure(kind, detail)`. The caller authenticates the lease, resolves the
actual pane and publishes the returned owner even on error. Record-shaped
identities do not grant authority. `capture_cursor_forget_lease` releases lease
descriptors on disconnect/revocation. Metadata queries do not drain here;
ingestion status must be derived by the composition owner from delivered-text
byte counters, with the incomplete-fragment limitation above. Output-only
publication must not advance configuration revision.

## Capture semantics and bounds

Selection uses logical lines. `Lines` endpoints are inclusive and relative to
the logical line intersecting current screen row zero; negative values select
history. Screen excludes history fragments. Alternate capture excludes primary
history. Joining soft wraps changes separators, not logical numbering. Retained
cell spaces are preserved. Styled output uses canonical SGR, not a replay of raw
child control sequences. Byte pages may split UTF-8 or SGR; concatenate first.

The cursor owner retains at most 16 descriptors, each for a fixed 30-second
monotonic lifetime. It caches no capture bytes. Tokens rotate on successful
pages and bind lease, pane identity/generation, child incarnation, content
revision and exact options. Expired/stale/mismatched/consumed tokens fail rather
than restart capture. Tokens are single-use, with no lost-reply replay guarantee;
on StaleRevision a caller starts a fresh capture and never mixes its pages with
the abandoned capture. Capacity and serial exhaustion fail explicitly. Payloads
are capped at 1 MiB; encoding visits one Unicode scalar at a time and emits at
most the requested byte window plus a one-byte continuation observation.
Bounded cells/tokens use the established `.chars()` traversal. Cells and CSI
parameters each retain at most 256 UTF-8 bytes.

Paging rescans the retained prefix to its offset, so many tiny pages can incur
quadratic total traversal. No measured latency/RSS claim is made. Ordinary
printable feeding checks touched cells only. Scroll/erase/resize, alternate
switches and synchronization release can compare affected rows or complete
bounded retained snapshots; this accompanies their existing row/history copies.
Frozen and alternate snapshots explicitly copy row, wrap and sparse-loss arrays.

## Source cycle 2: recoverable retention and compatibility

CSI parameters exceeding 256 UTF-8 bytes, or malformed CSI parameter input,
enter bounded discard mode through the final byte; ESC cancels the discarded
sequence and starts parsing again. A saturated `discarded_controls` diagnostic
records refusals. Ordinary printable output resumes, with no sticky failure.

Combining content exceeding 256 UTF-8 bytes leaves a bounded prefix and marks
only its affected cell. Sparse per-row column lists follow scroll, history,
alternate screens, synchronized frames, row edits and resize. Overwrite/erase,
history eviction and reset remove the corresponding loss. Strict captures fail
explicitly only when selected retained rows contain lost content; unaffected
ranges remain available. Interactive frames may render the bounded degraded
cell without disconnecting the session. Input and checked cleanup remain usable.

Legacy pipe history now selects its original tail even though shared CoreMux
capture maintains a separate VT view. Tail retention applies both the existing
200-line limit and a 1 MiB UTF-8-safe recent-suffix limit. `tail_truncated` reports
ordinary retention eviction; it does not disable subsequent output/capture.
`capture_retention_status(record)` returns bounded SDN text containing tail
eviction, discarded controls and lost-cell counts. Pagination `truncated` never
promises continuation into evicted history. Composition owners must surface these
retention diagnostics/limits; the frozen capture response schema is unchanged.

Invented capture-specific requirement IDs were replaced with selected
REQ-CMUX-003/005/006/008 and NFR-CMUX-005/006/007/008 IDs. Unicode paging controls
now use independent Han text bytes and explicit emoji byte vectors. Authored
retention/recovery controls and a real piped-child regression accompany the real
ConPTY scenario. None have executed.

## Evidence still required

Pure controls: `test/01_unit/os/smux_capture_cursor_spec.spl` and its authored
manual. Real-process scenario: `test/03_system/tools/coremux_capture_native_spec.spl`
and its authored manual. Both remain NOT_RUN. Native compilation, configured
provider execution, counter/array-copy controls, real ConPTY styles/history,
server lease integration, SPipe/manual generation, maintenance checks and
performance measurements remain pending. Source bounds and authored recovery
assertions are not measured memory, runtime ownership or terminal qualification.
