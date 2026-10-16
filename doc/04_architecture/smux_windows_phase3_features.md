# SMUX owner and client architecture

`server.spl` owns a single event loop and the process-local authoritative
service. It accepts loopback TCP clients, polls child output regardless of
attachments, retains bounded per-client input/output buffers, dispatches one
authenticated command and closes that request connection. Request EOF never
destroys service state. An authenticated `stop-server` ends the owner.

The layers are CLI arguments → transport owner → protocol dispatcher → service
API → shared layout/VT/PTY capabilities. Platform policy stays in existing
host providers. App source does not branch on Windows or Unix. Mutable service
state and socket handles stay in one execution domain; cross-process clients
exchange bounded immutable request/reply bytes. No worker shares `_svc`.

Each pending client retains a stream, raw request bytes, framed response bytes,
write offset, absolute deadline and authenticated shutdown flag. One read and
one write chunk per client per turn prevent an unbounded socket helper loop.
The owner treats ambiguous read errors as pending only until its deadline.
Response framing detects truncated output even when the server closes.

Production windows persist a selected named layout and canvas; geometry is
computed by `mux_rects.spl` using actual pane ids. Selection validates all panes
before one state commit. Arbitrary split/resize/close invalidates the selected
plan to manual. Composite capture caches each pane once and paints by rects.

This topology still depends on usable Windows TCP/ConPTY providers. Existing
core-C TCP stubs and blocking PTY writes prevent runtime admission. An explicit
independent foreground owner is not automatic daemonization, external terminal
rendering, job-object breakaway, live child resize or scrollback/copy mode.
