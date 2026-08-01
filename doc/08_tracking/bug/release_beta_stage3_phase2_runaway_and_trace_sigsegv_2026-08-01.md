# Release beta Stage 3 phase-2 runaway and trace SIGSEGV

Status: OPEN — blocks the non-macOS beta release.

## Observed behavior

The fresh main-working-copy bootstrap admits Stage 2, but its strict Stage 3 native build does not reach code generation. With the normal phase profiler it remains CPU-bound for 15m13s, grows to 9.7 GiB RSS, emits no phase log or object file, and produces no candidate.

A single bounded diagnostic used that exact admitted Stage 2 compiler with one thread, a fresh cache, phase/memory tracing, and `SIMPLE_NO_STUB_FALLBACK=1`. Entry-closure discovery completed for 1,758 modules. Phase 2 parsed `src/app/cli/main.spl`, began `src/lib/nogc_async_mut/cli/log_modes.spl`, and terminated with signal 11 (exit 139, 173 MiB maximum RSS).

## Evidence

- Diagnostic log: `build/mini_builds/release-beta-stage3-probe/probe.log`
- Compiler: `build/bootstrap/release-beta-final/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- Full retry output root: `build/bootstrap/release-beta-final`

## Required resolution

Localize and fix the phase-2 failure using bounded isolated probes. Do not accept seed fallback, missing output, or source-only substitution. After the fix, run one cache-preserving strict Stage 3 confirmation; successful Stage 4 and release verification remain mandatory before publication.

## Focused diagnosis and repair

Disabling `SIMPLE_STAGE4_STREAMING_SURFACES` on the identical 1,758-module closure removes the immediate second-module SIGSEGV: the non-streaming differential parsed continuously until its 30-second diagnostic timeout. The single-module `log_modes.spl` trace build also passes, excluding that source file as the cause.

The streaming driver began transient allocation tracking before the first call to `reset_all_pools()` and `ast_reset()`. In a native compiler, nil/zero-initialized parser globals therefore acquired their first backing arrays inside the reclaimable scope. Scope teardown freed those arrays while module globals retained their handles, and the second module dereferenced dangling storage.

`driver_prepare_transient_parse_scope()` now materializes and clears reusable parser pools and AST arenas before each phase-2/phase-3 transient scope begins. The streaming ownership contract requires this ordering in both paths. A fresh compiler confirmation is pending because another active shared-worktree Stage-3 build already consumes 13+ GiB; the lane's attempted rebuild was stopped during Rust authority compilation to avoid competing heavy writers and invalid RSS evidence.
