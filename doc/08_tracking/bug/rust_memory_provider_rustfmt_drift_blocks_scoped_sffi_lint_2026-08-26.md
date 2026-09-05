# Rust memory provider formatting drift blocks scoped SFFI lint

- **Status:** OPEN
- **Filed:** 2026-08-26
- **Area:** Rust seed interpreter SFFI provider
- **Severity:** medium — whole-file formatting gate cannot isolate owned edits

## Evidence

`rustfmt --edition 2021 --check compiler/src/interpreter_extern/memory.rs`
reports existing changes across unrelated memory-profile, heap, and mmap code in
addition to the MMIO provider. Reformatting the whole shared file in the MMIO
tranche would rewrite unrelated concurrent ownership and obscure semantic
review. The newly changed address-lift/test expressions were aligned with the
reported formatter output, but the whole-file command remains non-green and was
not rerun.

## Unblock condition

Land a separately reviewed mechanical formatting commit for the shared file,
then run the exact whole-file check once. Keep that change separate from SFFI
semantics so provider diffs remain auditable.
