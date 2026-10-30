# CoreMux capture source review — 2026-10-25

Status: **WARN / NOT_RUN — one P1 and three P2 findings open**. Independent first-cycle source review of the twelve paths pinned in `build/review/coremux-capture-source-v1.sdn`: seven production owners, two specs, two manuals and the source handoff report. All twelve hashes independently matched. Other authors' API/server, presentation and PTY-provider changes were preserved and are not qualified by this review. No compiler, native helper, product, test or watchdog was launched; no production edits or commit were made.

## Findings

1. **P1: retained child-output state remains unbounded, blocking the selected N2 goal.** In `vt_screen`, parser mode 2 appends every non-final character to `params` until a CSI final arrives. A child can stream an unfinished CSI indefinitely. `_put_char` appends every zero-width combining scalar to the preceding cell without a cell-string ceiling. `PaneRecord.ingest_pipe` concatenates the legacy tail and trims only by newline count, so one indefinitely long line grows forever. Row/history counts and the new sixteen-cursor/1 MiB-page limits do not bound these paths. This was disclosed honestly in the author report, but it is a required repair/explicit release blocker for NFR-CMUX-005 and the full bounded Smux goal, not an out-of-feature waiver. Define finite byte/scalar storage limits and observable overflow/refusal/discard behavior; add production-parser/tail controls before claiming whole-pipeline bounds. `_reply` also appends inside VT, but the normal pane owner clears replies after each bounded read batch into the bounded input queue; no fourth indefinitely growing live-pipeline path is claimed here.
2. **P2: new VT feeding changes legacy pipe capture semantics.** Before this change, piped output populated the retained tail and the screen stayed blank. The unchanged `PaneRecord.capture` chooses `vt_text(screen)` whenever nonempty. New `ingest_pipe` now populates that screen, so legacy pipe capture silently switches from its retained 200-line tail to the current grid, losing older requested lines and changing serialization. Preserve the legacy pipe capture selection separately from the new CoreMux VT capture, with a regression using more output lines than the grid height. The shared cursor may continue using the terminal model.
3. **P2: authored requirement IDs are not the selected requirements.** The specs/manual use `REQ-CMUX-CAPTURE-001..006`, which are not the accepted A/N2 `REQ-CMUX-001..012` / `NFR-CMUX-001..009` identifiers. Map the existing behaviors to the actual selected I/O, capture, capability, error and N2 requirements without inventing new user-selected requirements or claiming those full requirements executed.
4. **P2: the Unicode paging oracle does not independently establish preserved Unicode/styling.** The pure case compares paged bytes only with another call to the same `vt_capture_page` serializer. That verifies paging consistency but can pass if both paths corrupt the scalar or style/padding output identically. Add an independent expected byte/string oracle for the known 2x4 screen containing red Korean text and ASCII, including reset, padding and line separator. The native case uses ASCII markers and cannot supply the missing Unicode oracle. The author proposed explicit expected `ESC[0;31m` + Korean/ASCII bytes + reset/padding under the same bounded paging case.

All findings were sent to the author and parent before correction. The author is holding v1 source pending the complete batch and parent-selected overflow policy. The iterator spelling in the emitter follows an existing local precedent but has no native proof; using the established scalar-list owner under newly bounded cell/token storage is a reasonable source clarification, not an assertion that the current compiler has been shown to fail it.

## Reviewed ownership and behavior

`VtScreen` moves to a value-only module and remains exported through `vt_screen`. The capture helpers import those value types rather than importing the parser back, avoiding a type/parser cycle. Frozen and alternate snapshots explicitly copy nested rows and wrap arrays. Synchronized writes preserve the published frozen view and content revision until release; alternate capture excludes primary history. Native value-copy/array behavior still requires the authored execution controls, not source assumptions alone.

Ordinary printing compares touched character/style cells and wrap markers instead of serializing the full terminal on every character. Scroll/erase/resize and synchronization/alternate transitions compare their affected rows or retained views. Cursor movement and query bytes can advance ingestion without changing captured content. Every explicit PaneRecord reconstruction in the owned source preserves content revision, ingestion sequence and child incarnation. New attachment and retained failed-spawn reservations advance incarnation; close/retry preserve it. Native reads check counter headroom before ingestion, and attachment checks exhaustion before launch. Resize consumers must also refuse exhaustion before native effects; those consumers belong to the integration owner.

The ingestion sequence counts **delivered decoded UTF-8 text bytes**, before pipe newline normalization/cleaning. It is not a syscall raw-byte count: a provider may consume an incomplete UTF-8 sequence and retain decoder state while returning no text. API/server composition must use an honest definition of NotPolled/NoNewOutput/Ingested and must not advertise this sequence as proof of every raw native read. The author has agreed to correct the handoff wording.

Capture selection uses logical lines anchored to the logical line intersecting screen row zero, with inclusive endpoints and retained-history clipping. Screen excludes historical fragments. Joining suppresses only soft-wrap separators; retained spaces are preserved. Styled output emits canonical SGR transitions rather than replaying arbitrary child controls. Capture is a pure snapshot read: it neither drains a PTY nor increments metadata revision. Its returned observed revision and ingestion classification are supplied by the owning composition; constructing records is not lease authentication.

Continuation state is explicit and value-returned, not global. The caller must publish the returned cursor owner on error as well as success. Sixteen descriptors retain only identity/options/offset/deadline, not captured bytes. Tokens bind owner/incarnation/lease, pane, child incarnation, content revision and all capture options including page size. Monotonic time regression, expiry, content/incarnation mismatch, wrong lease, changed options, capacity and serial exhaustion have explicit errors. The fixed thirty-second expiry does not slide during paging; lease removal releases matching descriptors.

Successful pages consume their input token and issue a new serial token. If a reply is lost, replay of its old token is explicitly stale; the client must begin a new capture and must not concatenate that new capture with the old partial bytes. The frozen contract does not promise replayable page replies, so this is an explicit recovery policy, not an additional defect. Byte pages may split UTF-8 or SGR and require concatenation before interpretation. The serializer emits at most the requested window plus a one-byte continuation observation, but prefix rescanning can make many tiny pages quadratic in total traversal. No N2 latency/RSS claim is admitted.

Failed PTY spawn attempts close the acquired descriptor; failed/deferred close retains that exact descriptor in authoritative pane state, publishes `commit=true` and `cleanup_pending=true`, preserves the prior screen and blocks another spawn. A successful close clears it only after the provider reports completion. The pure retained-handle test uses data, not a fabricated native cleanup pass. The API must publish failure-side updates and preserve cleanup state in the request receipt; actual Windows completion and external terminal/quiescence proof remain separate provider/execution gates.

## Authored test and cleanup review

Eleven pure controls and one real ConPTY scenario are authored; **zero executed**. The pure controls invoke the real VT/parser, PaneRecord and cursor helpers for line selection, style retention, small-page continuation, lease refusal, stale/replay behavior, capacity, revisions, pipe normalization, synchronized copying, retained-handle values and history/resize alignment. They acquire no host resources. Findings 3 and 4 limit their requirement/oracle claims.

The native scenario actually calls the production pane spawn/poll/close owners with a PowerShell ConPTY child writing four known red lines into a three-row screen. It requires the first history marker, final marker, canonical red SGR and positive counters. Paging is performed on retained state after close, without another native read. Spawn/poll outcomes are collected and bounded close retries occur before post-acquisition assertions, including failed-spawn paths retaining a descriptor. Cleanup failure is asserted before success/output assertions. This is a real-process scenario, not a provider stub or skipped-host pass. It still needs an admitted runner/runtime/provider, bounded independent process ownership, actual terminal receipts and runtime assertions before any execution or cleanup PASS can be claimed.

The manuals are explicitly authored/NOT_RUN, not generated execution evidence. No source count, cursor bound, pure lease-shaped record, or unexecuted native scenario qualifies N2, endpoint authentication, actual Unicode rendering, child cleanup or the complete application suite.

## V1 source pins

| Path | SHA-256 |
|---|---|
| `src/os/apps/smux/service.spl` | `7cdab70afc4aec1aadbc38eb8d826ac2d9d402dab9db613dcc6d195565ca7cf1` |
| `src/os/apps/smux/pane_io_service.spl` | `4217e93eefd7380f106724cf36e882a5a08847eb3d76a0adc6d9620c50e14708` |
| `src/os/apps/smux/vt_screen.spl` | `bc3191f8920494f8cd1835fc68f5b4399d9d4934ff3a05f901d73f81b1c05f94` |
| `src/os/apps/smux/vt_types.spl` | `5b90163f5583372566f398362096ced766132b79db87e59a8a9e1fee9dfecd95` |
| `src/os/apps/smux/vt_capture_state.spl` | `bcdab3595cc097b82a660b45032ecee3df0e5d0cd1f8d28f6be58ebe53e405e7` |
| `src/os/apps/smux/vt_capture.spl` | `c9e38f75d2bb8376bad70cfa1b5185c950c3ec53b8edbc31f9d667c2f7cabeaf` |
| `src/os/apps/smux/capture_cursor.spl` | `db72354566d4d03f8341b4a51eecd9adceee90da3220b64e398f711711c86668` |
| `test/01_unit/os/smux_capture_cursor_spec.spl` | `0b8d522bc5081c9526ec1a82747c5a6d3d347f77cc82e0c9affe3f2cd1e3eeba` |
| `test/03_system/tools/coremux_capture_native_spec.spl` | `caab6c2c1a82e015a2fde05a6547f3f08ba9a8e3c57c7b04e172d1f9d76dda85` |
| `doc/06_spec/01_unit/os/smux_capture_cursor_spec.md` | `151318bcd924e00cd248fb0834c41b112cb29616130d830c9664b234988c6615` |
| `doc/06_spec/03_system/tools/coremux_capture_native_spec.md` | `66f4241c02ef04a7a9eb32f2676857219519dc7769d5dc5904dcb7f700f04d2b` |
| `doc/09_report/coremux_capture_source_2026_10_25.md` | `ca8b846cccaf65ceb4194e5c38ec1d925396def64cc8503c588c60d0402c42ab` |

## Focused cycle 2 source review

Freeze: `build/review/coremux-capture-source-v2.sdn`. All fourteen actual hashes match. Historical v1 findings and pins remain above. The four v1 findings are closed at the source level under the explicitly accepted recoverable-retention policy; no new scoped P0/P1/P2 finding was identified. **STATUS: WARN/NOT_RUN.** This is not whole-pipeline N2 qualification.

CSI retains at most 256 parameter bytes. Oversized or malformed input clears that buffer, increments a saturating diagnostic and enters allocation-free discard until a final character or ESC resynchronization. Subsequent ordinary output remains usable. Combining-cell retention checks the existing bytes plus the next scalar before append; overflow keeps a bounded prefix and marks the affected column once. Sparse lists cannot exceed the corresponding row width through the reviewed parser operations. Tail retention preserves at most 200 lines and a 1 MiB recent suffix, advancing a byte cut past UTF-8 continuation bytes. Its temporary work is bounded by retained state plus the provider-delivered chunk; the pure helper does not itself impose a caller-input length limit. `tail_truncated` remains observable and does not disable capture or input.

Loss-marker correspondence was traced through printable overwrite (including wide-cell partner clearing), partial/full erase, insert/delete characters, both row shifts, history append/eviction/limit changes, resize clipping, alternate save/restore, synchronization freeze/release and reset. The transformations move or remove markers with the corresponding stored cells. Alternate/frozen rows and loss lists receive explicit deep copies. The visible-view equality check includes visible and history losses, so adding/removing visible loss invalidates continuation state even when retained text happens equal; hidden synchronized changes remain unpublished until release. Resize clears frozen snapshots and fits saved alternate markers with their saved cells. Value-copy correctness still requires the unexecuted native controls.

Capture checks loss across the entire selected range even after its output byte page fills. It cannot return an apparently complete first page while hiding damage later in that selection. Damaged selections return Unavailable; unaffected selections remain usable. The legacy capture guards use the legacy selected-row rules, and the frame owner path retains degraded rendering without adding a fatal loss check. Input and close paths are not disabled by CSI/tail eviction or cell loss. Descriptor binding, fixed expiry and explicit stale-token/fresh-capture recovery remain as reviewed in v1; there is no new replay or authentication guarantee.

Legacy pipe capture now explicitly selects the tail while shared capture reads the separately maintained VT model. The authored regression requires thirty retained pipe lines beyond a two/three-row grid, rather than accepting only the current screen. Selected REQ-CMUX/NFR-CMUX IDs replace the invented capture identifiers. The Han control compares concatenated pages with an independently specified SGR/UTF-8 literal; the emoji control uses an explicit numeric byte vector, including style reset and display-cell padding. Both use real production serialization paths.

### Controls, cleanup and integration limits

Seventeen pure controls and two real-process scenarios are authored; **zero executed**. New recovery cases cover oversized/malformed CSI, selected versus unaffected cell loss, overwrite/erase, history eviction, frozen loss until release, and Unicode-safe tail retention. Alternate/edit/resize loss propagation was inspected in production source; there is no claim that every such path has an executed or dedicated new regression. The source titles/manual phrase “original bytes” means the decoded UTF-8 text supplied to the owner, as explicitly clarified in the handoff; it does not establish raw syscall-byte accounting.

The added native pipe scenario uses the actual spawn/poll owner and known PowerShell output. It closes the exact acquired process token with bounded retries before post-acquisition assertions, separately requires successful spawn and observed output, and compares retained tail content with fixed first/last markers and an exact thirty-row count. The ConPTY scenario preserves its close-before-assert path, including retained failed-spawn descriptors. Neither authored cleanup path is a terminal/quiescence receipt; an admitted provider, external bounded process ownership and actual execution remain required.

The new snapshot helper imports value/retention/history helpers, not the parser; the parser re-exports the existing public snapshot/type surface without a reverse cycle. The handoff correctly requires API owners to publish failure-side state, authenticate leases, release descriptors on revocation, guard counters before native effects and surface retention diagnostics. Those separately owned consumers are not admitted by this review. Bounded retained strings, sparse markers and cursor counts are source properties, not measured RSS/latency, provider cleanup or full application qualification. No compiler, test, native helper, product or docgen was launched, and no production source was edited.

### V2 pins

| Path | SHA-256 |
|---|---|
| `src/os/apps/smux/service.spl` | `103d39a56ee74b8747117846218adef54366a0f25657c5be5e55d0609f476b69` |
| `src/os/apps/smux/pane_io_service.spl` | `eaa536e8dc13b08f4a69691937985662e541f16959aa82ec5125447f7d843009` |
| `src/os/apps/smux/vt_screen.spl` | `72f299100177635bf47cea5b1b477bc58010ab6b9aaddbb3d41de2358452daa4` |
| `src/os/apps/smux/vt_types.spl` | `6a0023e8df7dab343529234eb67f378f16e8d9d71cb6d058bcca609425a1fcc5` |
| `src/os/apps/smux/vt_capture_state.spl` | `34d6e48f48d0d31442b2565177f44c18c7e6853e11d5f9801cd6c605cac41cfd` |
| `src/os/apps/smux/vt_capture.spl` | `fae33afd680dbe29295b7970bc570b12c0ae5390fa06d9e0caab19fbac33222c` |
| `src/os/apps/smux/capture_cursor.spl` | `f6a52bcbf7e92021235b660843dd1017aa3a96942cf9123525fc061b20b7016f` |
| `src/os/apps/smux/vt_retention.spl` | `56d6eb2e7dbcf54db2865992115b9a3bb1492eb6c0931d278ca35223e3835afc` |
| `src/os/apps/smux/vt_snapshot.spl` | `02282be013c51717e1a204fc182f987bd34941892976953885c1374bfad3cdc0` |
| `test/01_unit/os/smux_capture_cursor_spec.spl` | `ec5a1bcf27ecfe10742608c0537bda1a74bff6469d775f86ad86afb3c0cb2d48` |
| `test/03_system/tools/coremux_capture_native_spec.spl` | `5e21e4532d0e67111c64d9d1fd396e862a3fde8a645e636596be0a0d3b7df14b` |
| `doc/06_spec/01_unit/os/smux_capture_cursor_spec.md` | `c9c8fa34e5837983b0d670ed6a159af8c751f6912257e3c386ee8f604395535e` |
| `doc/06_spec/03_system/tools/coremux_capture_native_spec.md` | `d9fa666c4142c87833ba92fa6c4f9e6b4f0885f65a4909388db8efef5fa05922` |
| `doc/09_report/coremux_capture_source_2026_10_25.md` | `6a6ec5840632bf2274b98a07fd4be2e0bd4551366b385f43a948d5c8fa99d04f` |

## Publication normalization byte check

Independently compared the four retained originals under `build/review/owner-eof-normalization/before/` against their live files and `doc/09_report/coremux_owner_publication_normalization_2026_10_25.sdn` (receipt SHA-256 `2565f2bcdd5ed97b7abef079e52dfcfa37a1e9f61e046f66d97824309daaaa9c`). All eight actual before/after hashes match the receipt. Each live file is an exact byte prefix of its original: the presentation review loses one blank CRLF, the Windows launch review loses two blank LF endings, and `vt_types.spl`/`vt_snapshot.spl` each lose one blank LF. One original-style final line ending remains in every file. Both versions decode as strict UTF-8; every retained byte, BOM state, line body and interior line ending is unchanged.

The two source originals match the capture v2 pins above. The two review originals have full hashes `73d2e0a5bbc561b3a180b1c2fff5d20128abe59d2bb0aeb1b317378518d99212` and `b5b90061a975c7b6ea66a49867eff7c5f7c7ff2d7a8f8c9a8e11aa362085aca5`, matching the final-pin prefixes supplied by the publication owner. The receipt records all four final publication hashes; historical review pins remain unchanged here. No mismatch was found. This read-only byte/hash check repeats no behavioral review and adds no compiler, native, test or product execution evidence. **WARN/NOT_RUN remains.**
