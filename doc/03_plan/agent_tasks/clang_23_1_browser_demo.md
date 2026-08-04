# Agent Tasks: Clang 23.1 Browser Demo

- Pure-Simple backend lane: migrate discovery/capability/runtime compiler code
  and focused tests. Owner: `simple_backend_migration`.
- SimpleOS filesystem lane: migrate launchable guest Clang paths/manifests and
  focused tests. Owner: `simpleos_fs_clang`.
- Rust bootstrap lane: establish upstream LLVM 23 binding support and implement
  it or retain a precise blocker. Owner: `rust_bootstrap_llvm23`.
- Integration lane: provider helper, browser builder, CI/setup/docs, bootstrap
  and QEMU evidence. Owner and merge reviewer: root Codex.

Shared interfaces are `resolve_clang_23_1_toolchain` and
`validate_clang_23_1_toolchain`. Frozen manual steps are listed in the system
test plan. Setup/checker helpers must fail explicitly until implemented; no
placeholder pass is acceptable. Final review uses the highest-capability root
agent after all three sidecar reports are merged.
