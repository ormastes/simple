# tmux comparison scope

The primary comparison is the [official tmux manual](https://github.com/tmux/tmux/blob/master/tmux.1),
fetched by the Astra reviewer through context-mode on 2026-10-16 and indexed
as `smux-windows-audit-official-tmux-manual`.

Its server/client and detached-session behavior require the server to outlive
a disposable client. Windows and panes are separate concepts; layout changes
must affect geometry and visible output. Multiple attachment records do not
demonstrate multiple rendered clients. Copy mode, history, key tables and input
routing require their own explicit implementation and evidence.

The implementation comparison and precise residual source findings are in
`doc/09_report/smux_windows_tmux_audit_2026-10-16.md`. The local foreground
owner is an incremental implementation, not evidence of automatic daemon
launch, parent-job breakaway or full command-line/config compatibility.
