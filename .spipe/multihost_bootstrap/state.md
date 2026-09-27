# Feature: multihost_bootstrap

## Raw Request
$sp_dev use most cores. bootstrap on main of windows/linux(wsl) and free bsd with wsl like and push and land pr. and apply to release branch if needed.

## Task Type
todo

## Refined Goal
Bootstrap the current main source natively on Windows and WSL Linux and through a FreeBSD QEMU guest, repair any reproduced owner defects, verify fresh Stage 4 command capability, merge a reviewed PR, and backport fixes to the active release branch when that branch contains the affected code.

## Acceptance Criteria
- AC-1: Record the exact main revision, host/guest identities, available CPUs and memory, isolated build roots, source and compiler hashes, and supported command stages for all three rows. Use most available cores without parallel writers to one cache.
- AC-2: Windows Git Bash/MSVC completes the canonical full bootstrap from the main revision with a fresh non-stub Stage 4 binary; its logs and provenance receipts identify the build and exit status.
- AC-3: WSL Linux completes the canonical full bootstrap from the same main revision with a fresh non-stub Stage 4 binary and retained logs/provenance.
- AC-4: The canonical FreeBSD QEMU wrapper completes smoke and full bootstrap from the same main revision in a native FreeBSD guest, with guest CPU/job allocation using most safe available cores and retained overlay, serial, and bootstrap receipts.
- AC-5: Each fresh Stage 4 binary passes the bounded bootstrap-essential-tools smoke gate with test-runner, lint, duplicate-check, and aggregate markers. Platform handoff readiness runs Gate 1-6 in order and fails closed for missing Stage 3, stale, seed, or cross-built evidence.
- AC-6: For each reproduced failure, claim the bug record before editing, preserve the exact failing command and log, identify the pure-Simple owner first, add an exact and adjacent root-cause regression, and rerun only the failed shard with its producer-bound cache before the full row. Stop after three distinct fix/verify cycles.
- AC-7: Update affected research/architecture/design/plan under doc/, the reachable command guide under doc/07_guide/, feature and layer expert skill.md pages under doc/00_llm_process/, and open bug records under doc/08_tracking/bug/. Update generated/manual doc/06_spec and all affected Codex, agents, Claude, and Gemini workflow instructions if wrappers or evidence contracts change. Keep any unavailable host row active with an exact resume command and ledger owner.
- AC-8: Pass required focused checks, SPipe executable/manual evidence, direct env audits, compiler/lib/MCP/LSP checks where affected, and applicable whole interpreter tests. Commit only this lane's files, push the branch, satisfy protected PR admission, and merge the PR. Compare origin/release/1.0 with main; backport and verify any fix needed by that release line through its own PR.

## Scope Exclusions
None of the requested Windows, WSL Linux, or FreeBSD rows may be treated as PASS through a Rust seed, cross-build, stale binary, or unsupported command.

## Cooperative Review
N/A for sidecars: all three bootstrap rows use stateful host resources and producer-bound caches, and concurrent agent edits would obscure ownership. The primary agent is merge owner and final reviewer. The shared checker step is step_bootstrap_platform_handoff_readiness. Exact host commands and fail-fast assertions will be named in each executable spec before implementation. The primary agent reviews generated manuals.

## Phase
dev-done

## Log
- dev: Created state file with 8 acceptance criteria (type: todo).

- bootstrap: Source pinned to main edfa0daab038472319196313594265412f2b2f07 for Windows and WSL. Windows: 24 logical CPUs, 64 GiB RAM, requested 20 jobs and policy admitted 7. Linux WSL: 14 CPUs, 31 GiB RAM, requested 12 jobs and policy admitted 9.
- bootstrap: Windows Stage 2 exited 1 before compilation because LLVM 23.1.1 was not detected. A matching installed provider exists at C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc; set LLVM_SYS_231_PREFIX to its MSYS path for the next attempt. Log: build/bootstrap/multihost_windows/console.log. The materializer's 61 generated links were undone with its receipt-backed --undo; the worktree was clean afterward.
- bootstrap: Linux default backend exited at startup because LLVM 23 is absent. Cranelift reached fingerprint but failed on symlinked /usr/bin/llvm-config; setting LLVM_CONFIG=/usr/lib/llvm-14/bin/llvm-config reached Rust seed build. That build exited 101 because native Cargo 1.75 cannot parse Cargo.lock v4. Three distinct Linux attempts completed; do not repeat in this session. Logs: build/bootstrap/multihost_linux/console.log and logs/x86_64-unknown-linux-gnu/rust-seed-build.log in the WSL worktree.
- bootstrap: FreeBSD QEMU --preflight failed only at admitted_media. The required 14.4 amd64 BASIC-CLOUDINIT qcow2 and trusted SHA-256 are absent from the WSL shared-media path. The guest wrapper also hardcodes bootstrap --jobs=2 despite QEMU_CPUS=12; this needs a safe job knob before full acceptance.
- bootstrap: All three host rows remain active and unverified. See doc/03_plan/agent_tasks/multihost_bootstrap.md and doc/08_tracking/todo/multihost_bootstrap_2026_09_27.md.
