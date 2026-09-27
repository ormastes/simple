# Multihost bootstrap on main

Status: open, 2026-09-27. Owner: Codex. Final reviewer: Codex. Do not close or mark any host row PASS until fresh Stage 4 and essential-tool receipts exist.

Windows, WSL Linux, and FreeBSD QEMU remain active. Exact prerequisites, commands, and retained artifacts are in [the resume plan](../../03_plan/agent_tasks/multihost_bootstrap.md). Windows needs explicit LLVM 23 provider binding; WSL needs a native Rust/Cargo toolchain that accepts lockfile v4; FreeBSD needs admitted qcow2 media and a guest job policy that uses the requested cores. The current session reached the three-attempt cap before a full build passed.

Release branch `release/1.0`: no source fix exists to backport yet. Recheck whether each eventual fix affects that branch before opening a release PR.
