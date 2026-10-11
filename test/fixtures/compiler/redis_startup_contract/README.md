# Redis startup boundary regressions

Status: AUTHORED_UNEXECUTED. Bind the actual compiler, runtime archive and source
revision before execution. Neither source review nor the earlier failed Redis
sanity admits these fixtures.

- `text_bytes.spl`: native exit 0 requires exact `[65, 0, 90]` for embedded-NUL
  text, empty and singleton arrays, and an unchanged real libc `strlen` bridge.
  The former tagged-text-to-C-string conversion fails the first length check.
- `listener.spl`: one externally supervised process, no retries. Reject the
  invalid address, then require its own localhost ephemeral listener. The
  supervisor must verify the printed address belongs to that PID before
  connecting and sending ASCII `Q`, then require the exact three response bytes
  `[81, 0, 82]` (including the embedded NUL). Require exit 0 and complete process/socket
  cleanup under an overall deadline. The former C provider cannot accept a
  connection because it only binds. The former write bridge returns zero instead of writing
  tagged text. The SFFI aliases must reach the canonical owners.

The listener's accepted read additionally needs a supervisor deadline: the
source accept is bounded at 3000 ms, but a peer that connects without sending
must not leave a process running. Never count the banner alone as PASS.

Run `text_bytes.spl` against a qualified current runtime, and the listener against
both the repaired C provider and an existing already-listening provider when
available. Windows C networking remains unsupported; SimpleOS hosted TCP parity
is not established. Linux/macOS/BSD and Rust provider observations must be
reported separately. No platform result is implied by these authored fixtures.

The existing `IoError.message` field-provenance failure is separate and remains
OPEN. These scalar-descriptor tests deliberately isolate the two repaired
boundaries; they do not replace a later full Redis protocol regression.
