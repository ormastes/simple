# Stage 2 exact-source compile worker stack overflow (2026-08-14)

**Status:** fixed; focused prerequisite verification passed

## Root-cause category

Canonical Stage 2 Rust native-build aborts while compiling the exact source
`src/app/cli/bootstrap_focused_native_build.spl`. The retained log contains:

```text
thread 'compile-bootstrap_focused_native_build.spl' (...) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

`NativeBuildConfig::default()` supplies 16 MiB and
`compile_file_safe` passes that value explicitly to
`std::thread::Builder::stack_size`. Therefore `RUST_MIN_STACK` cannot raise this
worker's stack. This is a Stage 2 bootstrap/large-closure policy gap, not a
reason to raise every native-build worker unconditionally.

## Intended repair

Keep the ordinary native-build default at 16 MiB. Add an explicit CLI-owned
compile-stack size and make the canonical Stage 2 bootstrap command request a
64 MiB worker stack. Preserve the value in the Stage 2 provenance argument
hash and transcribed command.

## Required evidence

- Unit: MiB parsing accepts the Stage 2 value and rejects zero, malformed, and
  overflowing values.
- Integration: the production compile-worker builder creates the named exact-
  source worker with at least the requested stack.
- System: the canonical Stage 2 command and its provenance hash carry the
  explicit stack policy through the Rust native-build CLI into
  `NativeBuildConfig.stack_size`.
- No full bootstrap rerun in this focused prerequisite lane.

## Usage and reusable knowledge

- Provider token usage: unavailable (the provider exposed no per-task token
  receipt to this agent).
- Comparable completed-bug average: unavailable.
- Reusable cause: an explicit `Thread::Builder::stack_size` overrides the
  ambient Rust stack default; bootstrap policy must reach the owning config.

## Focused result

- Canonical Stage 2 now requests `--compile-stack-mib 64` in both the
  provenance hash input and the transcribed execution command.
- The ordinary `NativeBuildConfig` default remains 16 MiB.
- The overflow-checked parser has all decision branches covered: valid, zero,
  malformed, and host-size overflow.
- On Linux, the production compile-worker builder created
  `compile-bootstrap_focused_native_build.spl` with an OS-reported stack of at
  least 64 MiB.
- Full bootstrap was intentionally not rerun in this focused lane.
