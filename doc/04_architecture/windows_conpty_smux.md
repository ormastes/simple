<!-- codex-design -->
# Windows ConPTY for SMUX Architecture

`std.sys.pty` is the public pure-Simple capability and owns platform policy.
SMUX depends only on this module. Raw `rt_pty_*` symbols are private platform
providers: POSIX on Unix and ConPTY on Windows. Interpreter and native runtime
providers implement the same five-symbol lifecycle contract and keep an
internal logical-handle registry so Windows handles never masquerade as file
descriptors.

On Windows, open creates the ConPTY pipes and pseudoconsole; spawn attaches the
selected shell through `PROC_THREAD_ATTRIBUTE_PSEUDOCONSOLE`; read/write use the
owned pipe endpoints; close releases process, pipes, and HPCON. Partial setup
unwinds in reverse ownership order.

## Qualification boundary, 2026-10-16

The provider description above is the target contract, not proof that every
compiler generation links a native provider. Windows qualification must retain
the exact Phase 2 and Phase 3 producer identities, matching admission receipts,
successful SMUX links, and actual ConPTY child input/output. The Rust runtime
provider alone does not establish a core-runtime or self-hosted product pass.

The service API keeps session/window/pane state in one process. Attachment
records represent clients of that owner; they do not themselves implement
transport or a persistent daemon. A server owner independent of client stdin,
an authenticated transport, reconnect addressing, and independent client-exit
tests remain necessary before claiming tmux-style background persistence.

Pane split planning belongs to `layout.spl`; API validation and the single
authoritative state commit belong to `api.spl`. Running-child PTY resize is a
separate provider obligation and must not be inferred from VT-grid geometry.
