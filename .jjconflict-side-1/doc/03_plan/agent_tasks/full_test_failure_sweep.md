# Full Test Failure Sweep

## Goal

Run the complete repository test inventory while excluding files and fixtures owned by active development lanes. Repair the 10 open bugs that already have concrete evidence, convert the 3 open `N/A` bugs into reproducible tests, and add same-family regression coverage that prevents the original and structurally similar failures from returning. Work proceeds in parallel without mixing unrelated feature work. Difficult failures that cannot be repaired within three focused cycles remain open with retained evidence and an executable reproducer.

## Baseline

- Bug database snapshot: 26 active-table rows.
- Open bugs: 13.
- Repair set A: 10 bugs with an existing concrete test, fixture, document, or script reference.
- Reproducer set B: 3 bugs whose current `reproducible_by` field is `N/A`; each must gain a deterministic executable reproducer before its production fix is accepted.
- Closed rows: 12 fixed and 1 resolved duplicate.
- These counts are an issue inventory, not a current test-failure count. The executable failure count is established only by the frozen test manifest below.

## Exclusions

Before execution, enumerate active processes, worktrees, goals, and dirty files. Exclude only tests and owners explicitly claimed by an active development feature. Record every exclusion with owner, reason, path, and follow-up command; do not silently skip broad directories. Existing unrelated dirty files remain untouched.

## Parallel Lanes

1. Compiler frontend, parser, HIR, and type-system tests.
2. MIR, optimization, LLVM backend, and native-codegen tests.
3. Core libraries and runtime tests, excluding vendored sources.
4. Applications, CLI, MCP, LSP, and developer-tool tests.
5. Integration and system specifications.
6. Linux x86_64 bootstrap and essential-tool tests.
7. Linux AArch64/macOS ARM64 cross and native-runner handoff tests.
8. RISC-V cross-link and QEMU tests.
9. FreeBSD and SimpleOS QEMU tests.
10. Repository guards, generated specifications, documentation contracts, and test-quality review.

Each lane uses an isolated output/cache directory and writes a durable manifest containing command, runtime identity, target, status, duration, and first diagnostic. Parallel jobs must not share a writable compiler cache.

## Bug Work Packages

### Set A: Repair 10 Reproducible Bugs

For each of the 10 concrete open bugs:

1. Run the recorded reproducer unchanged and retain the pre-fix failure.
2. Confirm the first failing owner and separate cascades from independent defects.
3. Repair the smallest shared production owner.
4. Add an exact regression for the reported input.
5. Add at least one adjacent regression that exercises a different caller, data shape, boundary value, module route, or target using the same root-cause path.
6. Search the owning module and sibling implementations for the same unsafe pattern; add table-driven or parameterized coverage when three or more variants share the behavior.
7. Mark the bug fixed only after exact, adjacent, and failed-shard verification pass.

### Set B: Discover and Reproduce 3 `N/A` Bugs

For each of the 3 `N/A` rows:

1. Derive a minimal deterministic reproducer from the title, owner path, investigation log, and expected behavior.
2. Prefer a unit test at the owning boundary; use integration/native/QEMU coverage only when the defect requires that boundary.
3. Prove the test fails for the intended reason before editing production code. Reject crashes, timeouts, or unrelated diagnostics as false reproducers.
4. Update `reproducible_by` in the bug database to the executable test or fixture path.
5. Repair the owner and add an adjacent same-family regression as required for Set A.
6. If deterministic reproduction remains impossible after three focused attempts, retain `open`, document each disproved hypothesis, and replace bare `N/A` with a concrete diagnostic harness or blocked-platform procedure.

Current analysis inventory:

| Bug | Root cause | Reproducer |
|---|---|---|
| `llm-caret-tui-extern-gaps` | Canonical TTY detection already exists, but the terminal owner does not expose/install the existing atexit and signal latches, and production Caret I/O does not poll SIGWINCH. | `test/01_unit/app/llm_caret/chat_tui_terminal_recovery_spec.spl` |
| `itf-color-nontty-gap` | The live owner moved to `app.devhub.output`; after `NO_COLOR` and `ITF_FORCE_COLOR`, automatic policy returns true without checking stdout TTY state. | `test/01_unit/app/devhub/itf_output_color_tty_spec.spl` |
| `text-split-limit-ignored` | Both live Rust interpreter dispatch paths consume only the separator, while native MIR admits `split` only with one argument. | `test/01_unit/compiler/interpreter/nested_string_split_spec.spl` |

All three bug rows now carry concrete `reproducible_by` paths. The Caret recovery and ITF color rows are fixed with focused 3/3 passing evidence. Bounded split is implemented across pure-Simple evaluation, MIR/native runtime, and both bootstrap interpreter dispatchers, and the Rust compiler/runtime crates compile; its row remains open until a rebuilt admitted runtime passes the five-case behavior spec.

### Similar-Bug Prevention

Every root-cause family receives a compact regression matrix covering:

- the original failing input;
- a neighboring boundary or alternate data shape;
- a second caller/module/import route where applicable;
- malformed or unsupported input proving fail-closed behavior;
- another supported target or execution mode when the owner is platform-sensitive.

Tests must assert observable behavior or diagnostics. Source-text assertions may supplement but never replace executable evidence. A single test must not be duplicated across files merely to increase counts.

## Execution

1. Freeze the source revision, pure-Simple runtime path and hash, LLVM/Clang provider identity, target matrix, and exclusion manifest.
2. Run each unchanged acceptance command once. Preserve logs for pass, fail, timeout, crash, and unavailable-platform results.
3. Normalize failures by root cause. Cascades count once; unavailable native platforms are not failures and do not become passes through cross/QEMU evidence.
4. Claim each unrecorded root cause before production edits. Add an exact reproducer, one adjacent regression, and a same-family pattern scan.
5. Repair the smallest shared owner, rerun only failed shards, and stop after at most three verify/fix cycles per root cause.
6. If still failing, add or update `doc/08_tracking/bug/bug_db.sdn` with severity, status `open`, owner file/line, concrete `reproducible_by`, evidence, and proposed repair. A bare `N/A` is not an acceptable final state; use a diagnostic harness or explicit blocked-platform procedure when an ordinary executable test is impossible.
7. After failed shards pass, run the non-excluded aggregate suite once. Run direct env/process guards and ensure no executable `.spl` specifications exist under `doc/06_spec`.

## Completion Criteria

- Every frozen manifest row is `pass`, `blocked`, or `unsupported` with retained evidence.
- No unexplained failure, timeout, crash, placeholder assertion, or silent exclusion remains.
- All 10 initially reproducible bugs are fixed or retain a scoped three-cycle blocker report; no bug is silently dropped.
- All 3 initial `N/A` bugs have deterministic reproducers or explicit diagnostic/blocked-platform procedures, and their database rows are updated.
- All repaired failures have exact, adjacent, and same-family regression coverage.
- Similar-pattern scans cover sibling owners without creating redundant tests or weakening fail-closed behavior.
- Every unresolved difficult failure is represented once in the bug database.
- Merge owner reviews lane boundaries and commits only scoped fixes; a normal/high-capability final reviewer issues the final PASS/FAIL/WARN verdict.

## Ownership

- Merge owner: primary full-test sweep session.
- Final reviewer: separate normal/high-capability verification pass.
- Active-feature owners retain exclusive control of excluded files; this sweep must not modify or mark their tests complete.
