# SimpleOS network protocol layer expert

Pure Simple protocol owners live below the shared filesystem-launched server
entrypoints. For SSH RFC 4254, keep channel mutations in the per-session
`ChannelTable`, validate complete canonical wire messages before mutation, and
fail closed on malformed or stale channel identities. Host/runtime boundaries
may transport bytes but must not replace protocol decisions.

Current focused design:
`doc/05_design/os/ssh/ssh_channel_window_adjust_owner_v1.md`.
