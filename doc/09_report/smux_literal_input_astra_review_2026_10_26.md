# Smux literal bytes and Paste: independent source review

Baseline: `4b8a71f7d86549c9823e6e9b2b7dd8b2f25d522c`.
Initial v1 status: **WARN / NOT_RUN; one P2 native-test finding open**.
Twelve pure and three native cases are authored; zero executed. The child fixture
is NOT_BUILT. No production edit, compiler/test/native/helper launch, staging or
commit was performed in this review.

## Scope and evidence

Reviewed exactly the fifteen frozen manifest paths below: four provider/facade
surfaces, input queue, pane I/O changes, pure Paste codec and explicit-state
adapter, two specs, child fixture, manuals, plan and author report. Bounded
read-only dependency inspection followed the already-existing Windows byte
writer/pending owner and pane poll/status/drain path. All fifteen v1 hashes
matched, including manifest SHA256
`e73828636ab41801f7107d0a81707d348d9b4e87aa097e58aacb8c839c206881`.
Root's configured API/query candidate, client context, RenameWindow, SendKeys,
VT modes, full receipt ledger/provider admission and the Windows owner itself
are outside the implementation delta under review.

## P2-L3-01: channel test does not drive queued input after backpressure

`test/03_system/tools/smux_literal_input_spec.spl::literal_input_observe` uses
only `pane_input_status_state` in its mode=channel completion loop. That helper
may complete a provider-pending write and inspect remaining queue bytes, but it
does not invoke `_flush_input`. If initial `pane_send_bytes_state` retains the
new three bytes because an earlier write is still pending (including ordered VT
query replies from ready/output capture), or the byte writer accepts zero, the
local queue remains nonempty. Once pending clears, repeated status reads still
cannot submit it. The fixture times out even though normal server owner polling
would make progress. This is a source-visible test-driving defect, not evidence
that arbitrary bytes failed delivery or that the provider is broken.

Requested narrow correction: in that loop call the existing real explicit-state
owner poll/drain path, retain its returned state, then query input status and
retain that returned state too. Keep attempts/time bounds and cleanup-before-
assertions. Do not add a fake completion, direct writer bypass, forced queue
advance or invalid-byte child-fidelity assertion. The Unicode modes already
call pane_capture_state, whose drain includes flushing. Deterministic native
pending/partial-write failure evidence remains a separate unexecuted gate.

## Production source observations

- Generic Sys returns false/Err for raw literal support without invoking its
  UTF8-prefix/text fallback. Both Sosix families reexport the selected Sys symbols.
  The Windows facade delegates to the existing bounded byte writer and converts
  its negative result to Err; it introduces no extern or native buffer owner.
- Existing `windows_pty_write_some_bytes_v1` copies octets into retained owner
  storage, submits at most 4096 bytes to WriteFile, and returns zero for pending
  backpressure. Positive means provider-owned prefix, not child consumption.
  Its pending completion/error path remains queried before another queue flush.
  `literal_bytes_supported_v1=true` identifies installed mechanism only. Actual
  startup capability probe, current handle validation and qualification are
  independent; no complete CapNative/provider admission follows from that bit.
- PaneInput's new literal_pty field defaults false, is set only when nonempty
  bytes enter, survives enqueue/text/query-reply/partial-advance/sticky-failure
  constructions, and clears after complete local drain. Raw bytes never traverse
  a text conversion. When mixed with text or terminal replies, concatenation
  preserves existing queue order; literal mode removes the unusable text carrier.
- Retained capacity is 65536 bytes including consumed prefix, with a 4096-byte
  flush view. Invalid offsets/counts and allocation/overflow failures refuse;
  sticky errors retain the original byte queue and reason. Generic/pipe refusal
  cannot silently send the literal stream through process text stdin.
- Pure literal admission checks closing, exact session/window/pane ancestry,
  retained positive child/PTY identity and installed byte support. Effect path
  reserves bounded queue capacity and checks the actual child owner before
  publication/write. Errors after queue/native effects return commit=true with
  exact updated state; pre-admission/capacity/dead-child refusal returns prior
  state. Callers must publish commit-bearing errors exactly once; no API or
  receipt implementation is supplied or qualified here.
- Paste computes explicit bracket/Enter overhead before allocation and checks
  remaining queue capacity in one enqueue. The body stays bytes; bracket flags
  produce literal ESC[200~/ESC[201~ and append_enter produces CR. Neither flag
  negotiates VT mode, chooses shell syntax, nor implements SendKeys. Capacity
  refusal cannot partially enqueue a bracket opener.

## Test and claim boundary

Pure cases exercise actual production queue, codec and admission functions.
Synthetic positive PID/fd records enter only pure admission and never native
writers. They check exact NUL/high-bit/invalid UTF8 values, mixed text/reply order,
partial offsets, bounded chunk/storage, sticky errors, all Paste flag combinations,
capacity and owner/support negatives. They do not prove native liveness.

Native Unicode scenarios launch an actual configured console child, require its
readiness, submit exact supported UTF8/Enter, and require a computed output marker
only after the child matches its input and restores its console. Launch argv and
submitted body do not contain that final marker. Channel mode instead observes
queue/native completion for NUL/0x80/0xff; it deliberately makes no child stdin
identity assertion. ConPTY terminal interpretation is not a byte-transparent
arbitrary application-stdin contract. Admission/accepted status is never reported
as child delivery.

Returned launch/capture/send/status states are retained for owned cleanup before
assertions, including failed launch authority. External bounded Job/process-tree
receipts remain mandatory: scalar PID absence and provider pending zero do not
prove descendant cleanup or protect against PID reuse. Cleanup retry count alone
cannot preempt a blocking native call. Unsupported generic profile execution,
true partial/pending/error injection, saturation/fairness, actual compiler/runtime
lineage, canonical SSpec/docgen and broader smokes remain NOT_RUN. The source
reports/manuals keep these limits explicit; no full CoreMux/SendKeys route is
claimed. P2-L3-01 must be corrected before this candidate's test source is clear.

## Historical v1 pins

| Input | SHA256 |
|---|---|
| `src/lib/sys/pty.spl` | `100831c31e35670421b626867d896a4486ec75549fc2031558ae14fb143ab856` |
| `src/lib/nogc_sync_mut/sosix/pty.spl` | `b075672561c23f5b20fbbb966ad777b15666f3e8bdef68d6b22841bee5f855a6` |
| `src/lib/nogc_async_mut/sosix/pty.spl` | `592409b3927fb5b9de14185ef41f3ba3eb39dae4f95fdead17ce3c676219ac1b` |
| `src/providers/windows_native/lib/sys/pty.spl` | `9c4876c1dbd2fe68caaa26004aad1e2680e74255ccdd34625e790ce4a560f674` |
| `src/os/apps/smux/input_queue.spl` | `5259337b7feaa2ca06d8f32c6f494bf172d4c14d9caad5bb12f1011c001b4589` |
| `src/os/apps/smux/pane_io_service.spl` | `064e8e5d98fe89be48192070889786cdb4c8c4244490943bfc22111e89271abe` |
| `src/os/apps/smux/core_mux_input_codec.spl` | `bd5adf40a24f19f8024b2f6c000fdf48920bfddcea75a27c0734189cdbcdb1ff` |
| `src/os/apps/smux/core_mux_input_service.spl` | `fb130d417527c5a7da8b1a57c16f3a03b235dac51f4eeca5bb9bbccdf9539175` |
| `test/01_unit/os/apps/smux/literal_input_spec.spl` | `0a5e947204acf5c4efb117ebcfb84895175a86ab918103468d219488c068750f` |
| `test/03_system/tools/smux_literal_input_spec.spl` | `bbc9e44ade217fea03759729a85784f41c4afb42a9d4b235b52706bd33dce6c3` |
| `test/fixtures/coremux/literal_input_child.spl` | `8a4cfeb776f8d61bf5d4aec20105bc03caed9b47dda949889cba3b9982db5dc7` |
| `doc/06_spec/01_unit/os/apps/smux/literal_input_spec.md` | `44bfd4ab494a93a8da31d94527abbf3035c60099c08b18cd2915c212af1cc429` |
| `doc/06_spec/03_system/tools/smux_literal_input_spec.md` | `12bf86f0015c64aff90589a69403d9853ff54df07afc75ba83a75a8f121e606f` |
| `doc/03_plan/sys_test/smux_literal_input_2026_10_26.md` | `8eefee7ce69ddbb1b94f9289d0e4d77409e940c2638fb8f79ae7949b54f634b9` |
| `doc/09_report/smux_literal_input_source_2026_10_26.md` | `b57f4f15e225254c2e9a6048cbd7e3e82b6701b28ef757cfba3035f65fc9aa95` |

## Focused v2 rereview

Observed HEAD: `fd744829aea0e0d7f568cd2286702a1a9cf37c2d`.
Final source disposition: **P2-L3-01 CLOSED; WARN / NOT_RUN**.
No remaining scoped P0/P1/P2 finding. Twelve pure and three native scenarios
remain authored, zero executed; the child remains NOT_BUILT.

The v2 manifest SHA256 is
`44bbf64aa3a505ab5858a4a1e142af05e6fc0b725df244831ae778cdb1b316e8`.
All fifteen current file hashes matched. Exactly the system spec, its manual and
the author report changed; the other twelve pins, including all production
sources and the child fixture, are unchanged. The completed v1 production review
is retained rather than repeated. Root's concurrent API/key work is excluded.

The channel branch now calls `pane_poll_state(state, [], [])`, retains
`pumped.state`, then calls `pane_input_status_state` and retains `status.state`.
The fixture owns one nonclosing pane. Production polling drains at most eight
chunks for each retained child and invokes `_flush_input`; the existing pending
writer/remaining-queue path can therefore make progress on later iterations.
Sticky write errors remain in the returned state and prevent an idle success.
No direct native writer bypass, forced queue advancement or input-request replay
was introduced. The actual queue and native status remain the completion oracle.

The existing 200-attempt/five-second monotonic observation bound, invalid/backward
time stop and cleanup-before-assertion ordering remain. Cleanup retains every
updated state and its existing bounded retries; an external Job/resource guard
is still mandatory to contain blocking native calls and prove residual cleanup.
The manual continues to distinguish NUL/0x80/0xff channel completion from child
stdin fidelity. Unicode scenarios retain their separate real-child effect oracle.
The source correction does not constitute executed backpressure/failure evidence,
provider qualification, a full CoreMux route, or SendKeys implementation.

No compiler, test, native/helper/product launch, production edit, staging or
commit occurred during this focused rereview. Historical v1 findings and pins
above are preserved; the following pins identify the source-closed v2 candidate.

| Input | SHA256 |
|---|---|
| `src/lib/sys/pty.spl` | `100831c31e35670421b626867d896a4486ec75549fc2031558ae14fb143ab856` |
| `src/lib/nogc_sync_mut/sosix/pty.spl` | `b075672561c23f5b20fbbb966ad777b15666f3e8bdef68d6b22841bee5f855a6` |
| `src/lib/nogc_async_mut/sosix/pty.spl` | `592409b3927fb5b9de14185ef41f3ba3eb39dae4f95fdead17ce3c676219ac1b` |
| `src/providers/windows_native/lib/sys/pty.spl` | `9c4876c1dbd2fe68caaa26004aad1e2680e74255ccdd34625e790ce4a560f674` |
| `src/os/apps/smux/input_queue.spl` | `5259337b7feaa2ca06d8f32c6f494bf172d4c14d9caad5bb12f1011c001b4589` |
| `src/os/apps/smux/pane_io_service.spl` | `064e8e5d98fe89be48192070889786cdb4c8c4244490943bfc22111e89271abe` |
| `src/os/apps/smux/core_mux_input_codec.spl` | `bd5adf40a24f19f8024b2f6c000fdf48920bfddcea75a27c0734189cdbcdb1ff` |
| `src/os/apps/smux/core_mux_input_service.spl` | `fb130d417527c5a7da8b1a57c16f3a03b235dac51f4eeca5bb9bbccdf9539175` |
| `test/01_unit/os/apps/smux/literal_input_spec.spl` | `0a5e947204acf5c4efb117ebcfb84895175a86ab918103468d219488c068750f` |
| `test/03_system/tools/smux_literal_input_spec.spl` | `3d56fa30c38480a4a4645624cf7eea27aa2879788b0e7c6a45d201817cd59b81` |
| `test/fixtures/coremux/literal_input_child.spl` | `8a4cfeb776f8d61bf5d4aec20105bc03caed9b47dda949889cba3b9982db5dc7` |
| `doc/06_spec/01_unit/os/apps/smux/literal_input_spec.md` | `44bfd4ab494a93a8da31d94527abbf3035c60099c08b18cd2915c212af1cc429` |
| `doc/06_spec/03_system/tools/smux_literal_input_spec.md` | `256c66ac441a5473a0c1aab59338070e62f8520037c6670500420eeb0627fa49` |
| `doc/03_plan/sys_test/smux_literal_input_2026_10_26.md` | `8eefee7ce69ddbb1b94f9289d0e4d77409e940c2638fb8f79ae7949b54f634b9` |
| `doc/09_report/smux_literal_input_source_2026_10_26.md` | `85e013f96ffba2dcfd55c8b7a7dcf0039ac27c583990a2eb559ebb3f1a610c63` |
