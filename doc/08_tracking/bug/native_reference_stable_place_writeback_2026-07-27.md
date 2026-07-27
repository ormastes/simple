# Native Reference Stable-Place and Write-Back Semantics

## Status

OPEN. Prefix `&` and `&mut` can be represented through the flat AST, HIR, and
MIR reference marker, but native address semantics are not yet production
evidence.

## Problem

The native backends currently preserve the lowered local value for
`MirInstKind.Ref`. This matches the existing Rust bootstrap implementation and
works for heap-pointer-represented aggregates, but it does not prove that:

- a scalar local has a stable address;
- a reference to a field or index targets the original place;
- writes through a native reference are visible to later reads; or
- `&value as u64` has the intended cast precedence.

The MIR interpreter uses a local ID as its reference address, while the native
backends preserve the local value. That representation difference requires an
explicit contract and cross-backend tests.

The 2026-07-27 xhigh review confirmed the concrete loss points:

- `MirLowering.lower_expr` lowers the operand to a value local before emitting
  `MirInstKind.Ref`, so field/index place identity is already gone;
- `MirBuilder.emit_ref` gives the result the referent type rather than a
  `MirTypeKind.Ref` type;
- LLVM and C lower `MirInstKind.Ref` as value copies; and
- the flat parser currently groups `&value as u64` as `&(value as u64)`.

## Required Evidence

1. Define reference/cast precedence, including `&value as u64` and
   `(&value) as u64`.
2. Lower references from addressable HIR places rather than arbitrary value
   temporaries.
3. Verify scalar, aggregate, field, and index references in the MIR
   interpreter and native LLVM/C backends.
4. Prove native write-back with an executable test before replacing
   `unsafe_addr_of` in syscall output-buffer paths.

Until those checks pass, firmware output-buffer code must retain its existing
`unsafe_addr_of` boundary.
