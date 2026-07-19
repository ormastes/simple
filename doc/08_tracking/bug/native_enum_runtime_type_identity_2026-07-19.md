# Native enum runtime type identity

Status: fixed (2026-07-19)

## Reproduction

Two different custom enum types with the same variant ordinal and payload
compared equal when nested behind `Any`. MIR emitted runtime enum ID `0` for
every custom enum, and Pure and hosted C structural equality compared only
discriminant and payload.

The regression is pinned by `cross_target_enum_type_identity_ok` in
`test/fixtures/native_crossmodule_result_u8/main.spl` and by the focused C
runtime assertion in `test/01_unit/runtime/runtime_native_focus_test.c`.

## Fix

HIR preserves the canonical declaring-module identity for local and imported
enums. MIR derives custom enum IDs from that qualified name while preserving
reserved Result/Option IDs 0 and 1. A project-wide exact-name registry rejects
the i32 hash collision case before code generation. Pure and hosted C
structural equality compare enum ID before discriminant and payload.

The Rust seed has separate enum constructors that still emit ID 0; that
bootstrap-only sibling remains open and is not partially changed here.

## Evidence

- Focused hosted C runtime contract: PASS.
- Bootstrap portability source and shared-fixture contract: PASS.
- Explicit pure-simple-core execution and freestanding x86_64 QEMU proof remain
  pending with the existing deployed self-hosted compiler crash.
