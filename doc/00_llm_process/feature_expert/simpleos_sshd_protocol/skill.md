# SimpleOS SSHD protocol feature expert

The canonical filesystem-launched server is under `src/os/apps/sshd/` and must
remain Pure Simple at the SSH protocol layer. `ChannelTable` owns channel
lifecycle and window mutation. Route received window-adjust payloads through
`apply_remote_window_adjust`; do not duplicate wire parsing in the session
loop. The v1 contract is documented in
`doc/05_design/os/ssh/ssh_channel_window_adjust_owner_v1.md`.

Do not claim filesystem exec completion from SSH framing coverage. Kernel exec
ownership, target launch evidence, and protocol verification remain separate.
