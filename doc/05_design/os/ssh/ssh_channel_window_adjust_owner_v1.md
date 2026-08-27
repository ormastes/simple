# SSH Channel Window-Adjust Owner v1

The filesystem-launched Pure Simple SSH server delegates every received RFC
4254 `SSH_MSG_CHANNEL_WINDOW_ADJUST` payload to `ChannelTable`, the existing
per-session mutable channel owner. The owner accepts only the canonical
nine-byte message, a known open local channel, and a sum that fits in `u32`.
RFC 4254 permits a zero increment, which is accepted as a no-op. All checks
precede mutation; rejection closes the transport through the existing session
policy and cannot partially change a window.

This removes production-loop parsing duplication and keeps admission O(1)
after the bounded channel lookup (at most 256 entries), with no payload copy or
new retained allocation. Exec buffering and process ownership are unchanged.

## Static handoff

The focused spec covers accepted mutation and zero no-op plus trailing-byte,
overflow, unknown-channel, and closed-channel rejection. Runtime verification
was explicitly not run in this lane.
