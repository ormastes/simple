# Compiler CompileOptions Release Artifact Test Plan

Feature: FR-COMPILER-001.

## Coverage

- Source-level SSpec: `test/system/compiler_compile_options_field_access_spec.spl`
- Release artifact repro:
  - create `/tmp/t_clock.spl`
  - run `bin/release/x86_64-unknown-linux-gnu/simple /tmp/t_clock.spl`
  - run `src/compiler_rust/target/bootstrap/simple /tmp/t_clock.spl`
  - compare output
  - reject `CompileOptions.*` field-access failures and no-mode warnings
