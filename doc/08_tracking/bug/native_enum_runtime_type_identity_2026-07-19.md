# Native enum runtime type identity

Status: source-fixed; staged execution pending (2026-07-19)

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

The Rust seed's native constructors and pattern checks consume the MIR enum
name instead of treating every custom enum as ID 0. Runtime identity uses the
project `src` namespace even when compilation receives narrower
`src/compiler`, `src/app`, or `src/lib` source roots. Collision preflight runs
for mangled and `--no-mangle` builds, and synthesized variant checks retain
their `rt_enum_id`/`rt_enum_discriminant` runtime calls.

The Rust runtime compares and hashes the enum ID before the discriminant and
payload. Array payload hashes now follow the structural equality already used
by dictionaries, and runtime Option producers use reserved ID 1 consistently.
The shared fixture reads `rt_enum_id` directly and requires both custom IDs to
be at least 2 and different, in addition to retaining the cross-type inequality
oracle.

The Rust MIR-to-bytecode path now lowers `EnumUnit`/`EnumWith` through typed
`ENUM_NEW_TYPED` metadata carrying the full `u32` enum ID and discriminant. SMF
bytecode writers emit format version 2; both duplicated loaders retain version
1 compatibility and reject versions outside `1..=2`.

## Evidence

- Focused hosted C runtime contract: PASS.
- Bootstrap portability source and shared-fixture contract: PASS.
- The existing strict dual-backend parity runner is scheduled with the Rust
  seed in Linux, macOS, and Windows LLVM jobs after the seed/native-all build,
  and in the canonical FreeBSD full-QEMU bootstrap after those artifacts
  exist. Cross-compiled seed binaries remain build-only; no unsupported cross
  runtime is claimed. These are scheduled gates, not local execution evidence.
- Focused Rust bytecode tests are scheduled in hosted Linux, macOS, and Windows
  workspace jobs. Canonical FreeBSD bytecode execution remains pending. The
  native ARM32/AArch64/RV32/RV64 gates do not exercise this bytecode lane and
  are not claimed as evidence for it.
- Explicit pure-simple-core execution and freestanding x86_64 QEMU proof remain
  pending with the existing deployed self-hosted compiler crash.
