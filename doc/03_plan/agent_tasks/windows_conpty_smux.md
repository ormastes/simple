<!-- codex-design -->
# Windows ConPTY for SMUX Agent Tasks

- Raw native provider: ConPTY registry and lifecycle in runtime Rust.
- Raw interpreter provider: equivalent registry and dispatch.
- Pure-Simple owner: `std.sys.pty`, SMUX migration, and SPipe coverage.
- Merge owner and final reviewer: root Codex agent.
- Lower-model sidecars: N/A; platform ownership was split across peer agents.
