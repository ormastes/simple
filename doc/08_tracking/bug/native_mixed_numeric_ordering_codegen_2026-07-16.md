# Native mixed numeric ordering depends on operand order

**Status:** CLOSED-STALE (2026-09-12: source fix recorded but staged platform execution never completed; not re-verifiable from the record)

- status: source fixed 2026-07-16 -> CLOSED-STALE 2026-09-12; staged platform execution pending
- severity: high (possible silent wrong comparison)
- component: MIR numeric coercion, LLVM and Cranelift lowering

## Symptom

LLVM and Cranelift selected integer versus float comparison from the left
operand. An integer-left/float-right comparison could therefore truncate or
use the wrong predicate, while reversing the operands followed the float path.

## Resolution

MIR widens mixed signed-integer `<`, `<=`, `>`, and `>=` operands to f64 before
either backend. Mixed numeric `==` and `!=` emit their type-strict constant
result only after both operands have been evaluated. The strict-dual harness
covers both operand orders, equal boundaries, signed zero, NaN, and strict
equality.

Unsigned float ordering, signed/unsigned integer ordering, and unsigned
division, remainder, and shifts have their own strict cases. Linux runs the
full gate; macOS arm64/x64 and Windows x64 explicitly select this mixed numeric
case and its related unsigned cases. The existing cross-module Result fixture
also carries signed int/float operand-order and high-bit arithmetic controls
through LLVM and Cranelift on AArch64/RISC-V QEMU and FreeBSD without adding
duplicate builds. First staged platform-matrix execution is pending.

Unsigned integer/float ordering is tracked separately in
`native_unsigned_float_ordering_codegen_2026-07-16.md`.

## Triage 2026-09-12
Older than 45 days with the described staged-platform execution still pending; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
