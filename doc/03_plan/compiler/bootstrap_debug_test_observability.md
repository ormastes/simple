# Bootstrap Debug/Test Observability Plan

## Goal

Make long bootstrap failures diagnosable without adding work to the default
compiler path.

## Modes

- `off` (default): no new environment flags, files, scans, or subprocesses.
- `test`: progress records and coarse phase timing; no parser-expression trace.
- `debug`: `test` evidence plus detailed parser/compiler trace, successful LLVM IR
  retention, and memory snapshots.
- AOP call/assignment tracing remains separately opt-in because join-point
  discovery and event volume can materially affect compile time.

## Implementation

1. Add `--diagnostics[=off|test|debug]` to the bootstrap wrapper.
2. Make `test` and `debug` imply the existing low-overhead progress watcher.
3. Name Rust authority-build milestones so a long Cargo build is not reported
   as fingerprinting.
4. Reuse existing compiler flags; do not add default-path HIR/MIR/LLVM scans.
5. Bind diagnostic workers to an explicit absolute pure-Simple executable so
   isolated worktrees do not accidentally resolve a missing/different
   `bin/simple`.
6. Add opt-in coarse read/parse/lint/teardown timings to the lightweight check
   worker; suppress them in JSON mode to preserve stdout purity.
7. Document activation and evidence retention in the compiler guide, SPipe
   skill surfaces, native-build feature skill, and LLM wiki.

## Probe Findings (2026-08-03)

One pure-Simple check of `driver_log_helpers.spl` measured:

| Mode | Wall time | Max RSS | Output lines |
|------|-----------|---------|--------------|
| Default | 14.95 s | 221,384 KiB | 62 |
| Debug | 16.99 s | 222,300 KiB | 278 |
| Proposed light test flags | 17.53 s | 213,376 KiB | 62 |

The single samples do not establish a stable timing regression, but they do
show that debug adds 178 parser events while RSS stays comparable. The coarse
in-process profile measured parse at 256 ms of a 280 ms check command; the much
larger outer wall time is startup/module-loading and worker-launch overhead.
Therefore parser tracing remains debug-only and test mode uses coarse timing.

## Intensive Bug/Error Workflow

Use this sequence for every bootstrap/compiler bug or unexplained error:

1. Freeze and record source revision, host/target, driver executable, admitted
   child executable, runtime, cache, and failing command.
2. Reproduce with `--diagnostics=test` first. Retain progress events and coarse
   phase totals; for a focused source run `simple check --phase-profile <path>`.
3. Let the inventory reach its terminal manifest state when independent work
   can continue. Group failures by first real diagnostic and phase instead of
   reacting to every cascade.
4. Escalate only failing categories/files to `--diagnostics=debug`. Preserve
   parser/compiler trace, failing LLVM IR, memory snapshots, and the exact
   executable identities. Add scoped AOP tracing only when weave ownership is
   a live hypothesis.
5. Fix each root cause with exact and adjacent regressions. Retry failed shards
   with the same cache, then run one authoritative incremental build.
6. Return to default-off mode for admission/release evidence. Debug output is
   investigation evidence, never a substitute for Stage 4 sanity.

Do not run debug over the whole tree by default: the probe produced 178 parser
events for one small compiler file. Intensive use means consistent evidence on
every bug and deep tracing of the narrowed owner, not unbounded global logging.

## Verification

- POSIX shell syntax passes.
- Bootstrap help exposes the modes.
- The portability contract proves the mode is default-off, debug preserves
  LLVM IR, and Rust authority progress has a named milestone.
- Exact integration coverage proves explicit child identity, default-off check
  output, human phase events, and JSON suppression.
