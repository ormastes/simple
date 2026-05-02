# Bug: inline_asm tests race on a shared global block list

**Date:** 2026-04-28
**Severity:** flaky test — does not affect production, only CI stability
**Discovered by:** C1+C2 dedup pipeline run after the new helpers landed

## Symptom

Two tests fail intermittently when `cargo test --lib codegen` runs with default parallel test threads:

- `codegen::codegen_instr_tests::inline_asm::codegen_inline_asm_single_instruction_collects_cli`
  panics at `inline_asm.rs:33` — `assert!(c.contains("\"cli\\n\""))`
- `codegen::codegen_instr_tests::inline_asm::codegen_inline_asm_multi_instruction_collects_cli_hlt`
  panics at `inline_asm.rs:56` — `assert!(c.contains("\"cli\\n\""))` / `\"hlt\\n\""`

When run with `cargo test ... -- --test-threads=1`, **all 7 inline_asm tests pass cleanly.**

## Root cause

`crate::codegen::inline_asm::clear_inline_asm_blocks()` mutates a global registry. Multiple
test functions in the same module call `clear_inline_asm_blocks()` followed by populating
the registry and then asserting on `write_inline_asm_c` output. With parallel test threads,
test B's `clear_inline_asm_blocks()` can run between test A's clear and write, dropping A's
registered blocks before A reads the emitted C file.

## Why C1+C2 surfaced this

Before C1+C2, `test_jit_println_capture` and other codegen tests panicked from a different bug
(missing `call_runtime_1_void` variant, fixed in C1+C2 commit). The panic crashed the test
harness mid-run, masking the inline_asm race. With the void-helper bug fixed, more tests
complete and the race window opens.

## Recommended fix

Either:
1. Add a `#[serial]` attribute (the `serial_test` crate) to all 7 inline_asm tests, OR
2. Make `inline_asm_blocks` per-thread or per-test scoped, OR
3. Replace the global registry with a `&mut` parameter threaded through the inline-asm pipeline.

(Out of scope for the dedup pipeline — these tests are unrelated to the helpers.)

## Verification

```
cargo test --manifest-path src/compiler_rust/compiler/Cargo.toml \
  --lib codegen::codegen_instr_tests::inline_asm -- --test-threads=1
# 7 passed; 0 failed
```
