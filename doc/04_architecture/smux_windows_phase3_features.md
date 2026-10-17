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

Each pane owns a bounded retained input queue. Output-derived terminal replies
join that same queue; the event loop offers a bounded prefix rather than
waiting for the child to read. Queue offsets count bytes. The portable text ABI
submits only complete UTF-8 prefixes, while the Windows native provider retains
overlapped byte buffers until actual completion. Deferred failures are sticky
and observable independently of initial command acceptance.

Native Windows product composition orders `src/providers/windows_native/lib`
before the ordinary library root. Stable PTY/TCP facades resolve to pure-Simple
ConPTY/Winsock owners; applications retain one host-independent implementation.
TCP leases use reusable generation-tagged slots. PTY close invalidates public
leases but retains deferred or failed resource cleanup privately; shutdown
cannot certify clean completion while resources remain owned.

`window_layout_service.spl` projects snapshot geometry and performs backend
resize transactions before the API commits authoritative state. The API remains
the sole service writer. VT history is stored with the terminal snapshot and
serialized through `vt_history.spl`; synchronized frames freeze both current
screen and saved rows. Alternate-screen state does not enter primary history.

These providers and integrations remain source-only until actual Windows
execution. An explicit independent foreground owner does not establish automatic
daemonization, external terminal rendering, job-object breakaway, or interactive
copy/key-binding behavior. Live child resize and scrollback now have authored
implementations and executable scenarios, but their runtime gates remain open.
