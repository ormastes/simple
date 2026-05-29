# Compiler CompileOptions Release Artifact Local Research

Feature: FR-COMPILER-001.

## Findings

- Source-level import/name isolation for `CompileOptions` is already covered by
  `test/system/compiler_compile_options_field_access_spec.spl`.
- The remaining tracker blocker was the stale checked-in release binary.
- Refreshing `bin/release/x86_64-unknown-linux-gnu/simple` from the current
  bootstrap runtime makes the original repro output match bootstrap output and
  removes all `CompileOptions.*` field-access failures.

## Verification

The original `/tmp/t_clock.spl` repro now produces the same output from the
release and bootstrap binaries, and neither output contains `CompileOptions.*`
or `[WARN] no mode matched`.
