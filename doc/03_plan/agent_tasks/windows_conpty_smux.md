<!-- codex-design -->
# Windows ConPTY for SMUX Agent Tasks

- Raw native provider: ConPTY registry and lifecycle in runtime Rust.
- Raw interpreter provider: equivalent registry and dispatch.
- Pure-Simple owner: `std.sys.pty`, SMUX migration, and SPipe coverage.
- Merge owner and final reviewer: root Codex agent.
- Lower-model sidecars: N/A; platform ownership was split across peer agents.

2026-10-18 SOSIX routing repair: user-requested Astra owns the isolated alias,
product-import and fixture-source lane. Root owns compiler repair, admitted
producer selection, runtime qualification, final review and merge. No runtime
or release PASS follows from this lane's static checks.
