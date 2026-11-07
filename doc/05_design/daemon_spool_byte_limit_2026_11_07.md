# Daemon spool UTF-8 byte admission

Requirements: DAE-01 and HOST-01 from the existing distributed execution plan.
Scope: two serialized-message bounds in the existing V1 spool provider.

## Reviewed plan and implementation

Both writers used `content.len() > 1048576`; the no-follow reader enforces
1,048,576 bytes. Pending PR #7436 changes text len to Unicode codepoints, while
migration PR #7429 does not include this provider. A multibyte response could
then publish successfully despite exceeding the reader limit. The runner could
acknowledge its request, leaving an unreadable response.

Use existing `std.common.string_core.str_len(content)` for both writer checks.
This calls the runtime byte-length primitive already used by canonical
`boxed_text_bytes_checked`; it performs no encoding allocation. It is independent
of the text len semantic change and does not require the pending native byte_len
method lowering. Preserve ASCII ID length, collection counts, wire framing,
limit, publication ordering and V1 recovery behavior.

Astra reviewed the plan before implementation and approved this existing-helper
choice. No new daemon/codec/helper framework or compiler workaround is added.
This is migration prevention, not a claimed current failure: on the current
release text len still counts bytes, so the pre-change implementation can pass.

## Test and review scope

The shared fixture is `test/fixtures/daemon_sdk/spool_byte_limit.spl`; the SSpec
caller and authored manual mirror are under the daemon_sdk integration tree.
Request/response envelopes have fixed identity, numeric headers and one field.
ASCII framing constants include every header, separator and final newline.
Accepted files are checked independently through raw file-byte array length,
then decoded and compared with the expected payload. One byte over the limit
must refuse publication at a fresh path. A two-byte scalar repeated 2^19 times
must refuse both writes even though its character count fits below the limit.
No daemon process, acknowledgement hash, broad cleanup or foreign resources are
needed. Each case removes only its private temporary directory.

Merge owner: root. Plan and final source reviewer: Astra. Sidecar lanes: N/A.
Admitted SSpec/manual generation/core/lib/MCP/LSP qualification remains unavailable;
source-fix landing under the user's instruction does not certify runtime/release
readiness. Diagnostic build/runtime results are recorded below when available.

## Diagnostic evidence

Linux aarch64; source base `8e63eca53d5075100b7b121cca563db8ab1e430c`.
Unadmitted pure-Simple producer SHA256:
`afae09d224390a57d675a128a052626c3aa665c032481928332ebdc2859d7350`.
One native build and one run: both exit 0. All three fixture scenarios passed.
The run checks both writers, exact limits and multibyte refusal using real files.
No pre-fix failure or codepoint-migration runtime run is claimed.

Build options: `native-build --backend llvm --runtime-bundle core-c-bootstrap
--source src --source test/fixtures --entry-closure --entry
test/fixtures/daemon_sdk/spool_byte_limit.spl --threads 1 --mode one-binary`.
`SIMPLE_NO_STUB_FALLBACK=1`; private HIR/frontend/native caches and TMPDIR.
Build timeout 360 seconds; runtime timeout 60 seconds, process-group containment.
Logs/artifact: isolated worktree `build/spool-byte-limit/` (`build.log`,
`build.exit`, `run.log`, `run.exit`, `program`, `source.sha256`).

Working and staged environment guards, whitespace and executable-spec layout
passed. Admitted SSpec, generated-manual maintenance and broad core/MCP/LSP
checks remain NOT_RUN; the manual is authored and labelled accordingly. User
requested reviewed source-fix landing, not release qualification.

Recorded SHA256 inputs/artifact:
- `src/lib/nogc_sync_mut/daemon_sdk/protocol.spl`: `c0a583ee2c38969784bb98ad310fcbbb5bf38951a234a6f95eb03aa94122d27b`
- `test/fixtures/daemon_sdk/spool_byte_limit.spl`: `55bbe6724262bcb784930f735b6bd1508164ba036e7a6d24ce3a73726910d2cf`
- `build/spool-byte-limit/program`: `28f8298f4335fd4adc0f2b66d8b78b04d13bc37a0bcedab0998131af41358882`
