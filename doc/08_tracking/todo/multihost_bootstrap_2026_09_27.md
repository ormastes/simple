# Multihost bootstrap on main

Status: open, updated 2026-09-28. Owner: Codex. Final reviewer: Codex. Do not close or mark any host row PASS until fresh Stage 4 and essential-tool receipts exist.

Windows and WSL Linux remain active. FreeBSD QEMU is deferred at the user's request. Exact commands and retained artifacts are in [the resume plan](../../03_plan/agent_tasks/multihost_bootstrap.md). Windows built a Stage 2 compiler and passed its frontend and receiver smoke, but the compiler test matrix refused delegated rows without an MC/DC-off waiver. WSL built and linked Stage 2, then its frontend smoke aborted in the AVX-512 instruction owner. Neither host has Stage 3, Stage 4, or essential-tool PASS. The session retry cap has been reached.

Release branch `release/1.0`: no backport was applied. The Rust flag forwarding omission also exists in its older bootstrap script, but release-line verification is still required before a backport.
