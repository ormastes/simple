# SSH channel request authority v1

## Boundary

`SshSession.channels` is the sole mutable owner of channel lifecycle and
terminal-request state. Wire recipients are untrusted scalar handles. A request
is dispatchable only when `ChannelTable.is_open_session` resolves that handle
to an existing open RFC 4254 session channel.

## State and bounds

Each bounded channel slot records one `ChannelTerminalRequestV1`: `None`,
`Shell`, `Exec`, or `Subsystem`. `begin_terminal_request` is the only commit
operation and changes `None` exactly once. PTY state is separately one-shot and
must precede the terminal request. Window changes require the same channel to
own both a PTY and a shell. The existing 256-channel session ceiling bounds all
new state; request processing adds no global registry or unbounded queue.

## Wire policy

- Unknown, closed, and forwarding-channel recipients never dispatch and never
  borrow the session's active remote channel ID.
- `shell` has an empty body; `exec` has one non-empty command of at most 4096
  bytes; `pty-req` has a 1..64 byte terminal name, fixed geometry, and at most
  1024 bytes of modes; `window-change` has exactly four uint32 values.
- `env` is rejected until a bounded validated environment owner exists.
- A deferred exec reply is retained as one boolean and emitted only after the
  shallow launch path reports that command resolution admitted an execution
  attempt. Rejection does not claim `CHANNEL_SUCCESS`.

## Loader separation

This change does not create loader authority. ARM64 request-context and
executable-token identity still require a future loader-owned joint grant. SSH
channel state remains protocol admission evidence only.
