# Rust seed enum runtime type identity

Status: source-fixed; focused Linux Rust execution passed, hosted matrix scheduled.

The Pure implementation remains canonical. Rust LLVM and Cranelift constructors
reuse the same stable qualified-type ID, and structural equality/hashing include
that ID. The bytecode compiler now lowers `EnumUnit`, `EnumWith`, and variant
`PatternTest` through `ENUM_NEW_TYPED` and `ENUM_MATCH_TYPED`, preserving the
full `u32` enum ID and discriminant.

Legacy `ENUM_NEW` and `ENUM_MATCH` retain their version-1 wire layouts. SMF
writers emit version 2, while both duplicated loaders accept versions `1..=2`
and reject versions outside that range.

Focused compiler/runtime tests cover unit and payload constructors, qualified
cross-type mismatch, full-width IDs/discriminants, legacy enum ID 0, and SMF
version compatibility. Hosted Linux/macOS/Windows jobs schedule the same Rust
tests. The canonical FreeBSD full-QEMU wrapper now schedules the two typed-enum
bytecode compiler/VM regressions with a strict 2/2 summary; live FreeBSD
execution evidence remains pending. Native
ARM32/AArch64/RV32/RV64 gates do not exercise this bytecode lane.
