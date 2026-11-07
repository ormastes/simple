# Custom-native x86-64 integer overflow arguments

Status: source repair independently approved; runtime verification pending.
No Simple test, native execution, or production-readiness PASS is claimed.

## Concrete failing boundary

`src/compiler/70.backend/backend/native/isel_x86_64.spl` previously pushed
overflow arguments in ascending index order. In an eight-integer-argument
call, argument eight therefore occupied the location expected for argument
seven. An odd overflow count subtracted eight modulo sixteen bytes before
CALL, breaking the alignment established by the prologue and register
allocator. The callee prologue initialized only the first six arguments;
`LocalKind.Arg(6)` and later were never assigned their incoming stack values.

The source reproducer calls `eight(1, 2, 3, 4, 5, 6, 7, 8)` and requires
`g * 100 + h == 708`, distinguishing argument order. Companion boundaries
cover six register arguments, one negative overflow argument, and three
distinct overflow arguments.

## Repair and prevention

The caller reserves eight padding bytes for an odd overflow count, before
pushing overflow arguments right to left. Cleanup restores both argument
words and padding. The callee loads scalar overflow argument index `n` from
`[RBP + 16 + (n - 6) * 8]`; the existing hidden result pointer shift remains
part of its ABI index calculation.

`test/01_unit/compiler/backend/x86_stack_argument_abi_spec.spl` inspects real
selector MachInst output before allocation: zero through six arguments,
seven/eight/nine boundaries, direct and indirect calls, optional scalar
return destinations, exact cleanup, and reordered argument locals.
It also protects the admitted five-scalar call boundary with a hidden
frame-vector result pointer. This does not extend frame-vector admission:
the planner continues rejecting overflow under its existing policy.

`test/fixtures/compiler/x86_stack_argument_abi/main.spl` is the source
reproducer with four runtime assertions. It must be compiled with the custom
native backend and executed by a source-matched admitted pure-Simple producer.
LLVM/Cranelift or interpreter execution cannot prove this backend repair.

## Verification limits

No admitted source-matched self-hosted runtime is available in this session.
The selector spec and source fixture have therefore not executed. The source
fixture can additionally encounter the independently documented generic
spill-lowering defect when more than five values are live across a call;
selector tests isolate argument placement from that defect. Existing
floating-point calling/return classification and aggregate lifetime/return
limitations remain separate, unverified work. This change does not repair them.

Baseline owner blob: `e8651602d66d098b01c7031ef8a5ecf06890a989`, matching the
release snapshot reviewed by the packaging owner. Independent reviewer:
`/root/astra_linker_final` approved the narrow repair and authored regressions
with no blocking findings. Reviewed source SHA256:
`255d8e48c7cecd6528d08b03b871fc567337e6506c147486692de2fc4c231259`.
Reviewed selector spec SHA256:
`9d6c65398f8ab0b61a6f83df1da11353fb45eec0ef42b9cfdc87bd60f0016fa9`.
The approval is source-only; runtime qualification remains pending.
