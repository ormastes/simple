# Feature: c-runtime-exclusion-analysis

## Raw Request
Work in /home/ormastes/dev/pub/simple on tracker doc/08_tracking/bug/c_runtime_exclusion_analysis_2026-05-18.md. You are not alone in the codebase: do not revert others' edits. Own only C runtime exclusion audit docs/config/tests directly related to tracker plus .spipe/c_runtime_exclusion_analysis/** and tracker. Use $sp_dev workflow. Goal: reduce or close open audit items with evidence, preserving pure Simple as main and Rust/C only as seed/tooling or unavoidable runtime dependency. Report changed paths, commands, remaining blocked items.

## Task Type
code-quality

## Refined Goal
Reduce the open C runtime exclusion audit surface by updating the tracker with current evidence for removable, platform-gated, and still-blocked C runtime files while preserving pure Simple as the main implementation direction.

## Acceptance Criteria
- AC-1: The tracker records current evidence for at least one open audit item and either closes it or narrows its blocker with concrete commands or file references.
- AC-2: Any changed files are limited to `doc/08_tracking/bug/c_runtime_exclusion_analysis_2026-05-18.md` and `.spipe/c_runtime_exclusion_analysis/**`.
- AC-3: The tracker distinguishes pure Simple primary code from Rust/C seed, tooling, platform, or unavoidable runtime dependencies.
- AC-4: Verification commands are run or documented with explicit blockers when not run.
- AC-5: Unrelated worktree edits are preserved and not reverted.

## Scope Exclusions
No source-code deletions, runtime ABI rewrites, broad build-system refactors, or edits outside the tracker and `.spipe/c_runtime_exclusion_analysis/**`.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: code-quality)
- audit: Closed `hosted_cocoa.c` and `hosted_win32.c` as stale unbuilt C duplicates based on active `spl_hosted_runtime` Rust exports and path/build-reference evidence.
- verify: `sh scripts/install-spipe-dev-command.shs --check` passed.
- verify: `cargo check --manifest-path src/runtime/hosted/Cargo.toml` passed.
- verify: `bin/simple test test/unit/os/compositor/hosted_backend_cocoa_spec.spl` passed 7 examples.
- verify: `bin/simple test test/unit/os/compositor/hosted_backend_win32_spec.spl` passed 6 examples.
- verify-blocked: `cargo test --manifest-path src/runtime/hosted/Cargo.toml` is blocked by an existing Rust unit-test type mismatch in `src/runtime/hosted/cocoa.rs` (`rt_cocoa_window_new` now expects `i64`, test passes `std::ptr::null()`); source/test fix is outside this doc-only audit pass.
