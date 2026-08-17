# LLM Caret Native Closure Admission Failure — 2026-08-11

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Symptom

`bin/caret --help` and `bin/caret --tui` correctly fail closed with exit 127:
no cached native Caret artifact exists. A cache-preserving native closure probe
then exposed a linker failure rather than an executable Caret surface.

## Root Causes

1. `src/app/llm_caret/messaging/cli.spl` imported `process_run_inherit` through
   `app.io.mod`, which does not export it. Native lowering emitted the bare
   `_process_run_inherit` symbol instead of the runtime-owned
   `_rt_process_run_inherit`. The import now names
   `app.io.process_ops.{process_run_inherit}` directly.
2. The core-C runtime had no terminal ABI provider for raw mode, terminal size,
   TTY detection, or byte input. `src/runtime/runtime_terminal.c` now owns that
   ABI and both core-C archive builders include it.
3. A full Caret closure still needs an admitted simple-core archive for the
   tagged filesystem ABI and a duplicate-safe native thread callback provider.
   The legacy broad `runtime.c`/`runtime_thread.c` objects must not be added
   blindly because they overlap existing core-C owners.

## Why Existing System SSpec Did Not Catch It

The cached CLI and PTY SSpecs assert the qualified-artifact success path, but
their prerequisites never had a mandatory native-entry build gate. The plan
described missing artifact execution as "blocked" and recorded zero scenarios,
so the unbuilt delivery artifact was not promoted to a release failure.

## Prevention

`scripts/check/check-llm-caret-native-closure.shs --check` is the required
pre-SSpec release gate. It rejects bootstrap/seed runtimes, absent or ambiguous
simple-core archives, stub fallback, failed entry-closure builds, missing
artifacts, and unresolved Caret ABI symbols. It retains build arguments,
stdout/stderr, exit status, `nm` output, and provenance under
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_native_closure/`.

The corresponding modern SSpec and manual document the positive admission
path. A missing artifact is no longer a skipped or zero-execution result: the
direct gate exits 1 with `failure_class=release_gate`.

## Required Completion Evidence

1. A self-hosted, non-seed runtime and a matching simple-core archive make the
   native closure gate pass.
2. The resulting artifact is installed with provenance for `bin/caret`.
3. Cached CLI, cached plain hidden-CLI, and PTY TUI system checks pass with
   retained output and ANSI evidence.
