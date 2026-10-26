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
