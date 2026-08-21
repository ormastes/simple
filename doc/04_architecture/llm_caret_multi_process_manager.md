# LLM Caret Bounded Multi-Process Manager

The `MultiCaretManager` value is the single parent authority for a finite batch
of Caret CLI children. Requests cross the launch boundary as copied immutable
values. Successful spawn returns opaque PID handles into the parent-owned
`AgentTeamProcess`; children never mutate manager state and publish no shared
heap values.

Admission is bounded to 1..16 processes and rejects the complete batch before
spawn when it exceeds capacity. A partial spawn is failed closed: the parent
attempts cleanup of every returned handle and publishes only a
`launch_rolled_back` state. Poll and stop create replacement manager values;
only these parent transitions inspect or terminate handles. Terminal stop is
idempotent at the manager boundary.

`AgentTmuxEmbed` is derived display state. It copies process identifiers and
statuses into pane commands, but it never owns a PID or performs lifecycle
operations. This preserves one process authority while allowing a terminal-pane
presentation. It is not the `os.apps.smux` production adapter.

The adapter deliberately remains a finite launch owner, not a persistent
supervisor: restart policy, unbounded queues, live PTYs, and cross-process
mutable transport are outside this contract.
