# Native mixed numeric ordering depends on operand order
## Closed 2026-09-16 — ...erand order - status: source fixed 2026-07-16; staged platform execution pending - severit

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- status: source fixed 2026-07-16; staged platform execution pending
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

## Verification 2026-11-25 (p2w4-ag lane, release/1.0.0 @ 63e791180d3)

Re-confirmed closed by source inspection on Windows: the MIR mixed-numeric
handling described in the Resolution section is present at
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:7218-7266` —
`mixed_numeric_kinds` emits the type-strict constant for `Eq`/`NotEq`
(lines 7223-7233) and widens both operands of ordered comparisons to f64,
with unsigned int operands retyped to U64 first so the backend selects the
unsigned int->float convert (lines 7258-7266). The strict-dual harness was
not re-executed on this host (pinned-seed/native-build lane unavailable);
status remains Closed.

