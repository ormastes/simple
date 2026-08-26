# file_read has a single return type

Static guard for the TEXT read family, sibling of the byte-family guard
`test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl`.

`file_read(path: text)` had 23 definitions across two incompatible return types:
20 `-> text` and 3 `-> text?`. The compiler's flat function registry is keyed on
NAME ALONE, so which definition a call site received depended on the import
closure of the compiling module, and nothing at the call site changed. A caller
written against `-> text` has no nil branch, so being handed the optional
definition drops the absence path silently.

The three optional definitions were module-local and non-exported. They were
renamed to `file_read_opt`, removing the name collision.

Requirements: REQ-IOREAD-007, REQ-IOREAD-008, defined in
`doc/03_plan/sys_test/scv_render_file_read_coverage.md`.

## file_read has a single return type

### Positive control: the scanner finds a definition that certainly exists

1. Count definitions of `file_read_opt`; expect at least one.

### Negative control: the scanner does not match a symbol that cannot exist

1. Count definitions of a symbol that cannot exist; expect zero.

### No definition of file_read returns an optional

1. List files defining `file_read` with an optional return; expect an empty list.
2. Count them; expect zero.

### Every definition of file_read shares the plain text return type

1. Count all `file_read` definitions.
2. Count those returning plain `text`.
3. Expect the two counts to agree, and at least one definition to exist.

### The optional-returning reads live under their own name

1. Count all `file_read_opt` definitions.
2. Count those returning the optional shape.
3. Expect the two counts to agree.

### The canonical text read is still exported exactly once

1. Count `pub fn file_read` definitions; expect exactly one.

## app.io.mod re-exports both byte-read shapes

### Negative control: the scanner does not match an absent symbol

1. Count shim lines mentioning a symbol that cannot exist; expect zero.

### Re-exports the canonical [u8] byte read

1. Count shim import and export lines naming `file_read_bytes`; expect two.

### Re-exports the raw [i64] byte read

1. Count shim import and export lines naming `file_read_bytes_i64`; expect two.

## Scope

This guard asserts SINGLE RETURN TYPE, not single definition. Twenty same-named
`-> text` definitions remain; they are mutually substitutable, so no misdispatch
hazard exists. Converging them is separate tracked work and is deliberately not
asserted here — an assertion failing for work this change did not attempt is
noise, not a guard. The sibling doc records that converging the byte family was
attempted and reverted because it hung the compiler.

## Execution status

**Not executed.** Authored while no qualified pure-Simple runtime was available;
the Rust seed is not admissible evidence and the bootstrap stages segfault (see
`doc/08_tracking/bug/origin_main_seed_unbuildable_duplicate_heap_counter_symbols_2026-08-16.md`).

All nine asserted facts were nevertheless verified by running the guard's own
oracle commands directly: optional count 0, plain 20, total 20, `file_read_opt`
3 (all optional), `pub fn file_read` 1, and both byte readers present on two shim
lines each. That establishes the facts are true — it is **not** evidence that the
spec harness ran, and no pass is claimed.
