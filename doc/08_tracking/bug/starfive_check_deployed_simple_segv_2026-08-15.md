# Deployed Simple checker crashes on StarFive implementation files

Status: OPEN / deployed full-CLI tooling defect; not the StarFive builder

- Date: 2026-08-15
- Command: `bin/simple check src/lib/nogc_async_mut/fs_driver/ramfs.spl ...`
- Executable: `/home/yoon/simple/release/x86_64-unknown-linux-gnu/simple`
- SHA-256: `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
- Result: exit 139 while checking the first file, before any source diagnostic.

This reproduces the already-known deployed self-host environment-write/miscompile class referenced by `scripts/lib/simple-compiler-select.shs`. It blocks running the generated SSpec through the deployed full CLI. It no longer blocks the board build or physical acceptance: a provenance-admitted pure-Simple Stage 3 compiler builds the ELF, and the canonical contract/self-test/live checker passes. Do not use the Rust seed as a substitute for repairing the deployed full CLI.

---

## Triage classification 2026-08-17 — DEFERRED: requires physical StarFive board + a fresh bootstrap

Reviewed in the second-pass backlog sweep. Not actionable from this session:
the SEGV is in a deployed binary on RISC-V hardware not present on this host, and reproducing it needs a rebuilt/redeployed compiler. No code change is possible without that, so no
speculative fix was attempted. Classification recorded here so future sweeps
skip it in O(1) instead of re-deriving the blocker. Status remains OPEN.
