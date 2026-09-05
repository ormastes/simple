# MIR used-local collector V1

The canonical used-local collector lives in
`src/compiler/50.mir/mir_used_local_collector.spl`.  It exposes four pure
helpers:

- `mir_used_local_ids_operand_v1` returns the local behind a `Copy` or `Move`
  operand and no local for constants.
- `mir_used_local_ids_place_v1` returns the place root plus every dynamic
  `Index` projection local.
- `mir_used_local_ids_instruction_v1` explicitly classifies every current MIR
  instruction variant.
- `mir_used_local_ids_terminator_v1` explicitly classifies every current MIR
  terminator variant.

The instruction collector has no permissive fallback arm.  A new opcode must
therefore be given a deliberate use policy at this MIR boundary before it can
be consumed by an optimizer or another liveness-sensitive pass.  The collector
is conservative for inline assembly (both input and output operands) and for
`ResultMatchSemantic` local references; retaining an extra definition is safer
than erasing a value that a verification or target-specific consumer needs.

`test/01_unit/compiler/mir/mir_used_local_collector_spec.spl` provides the
operand/place matrix, representative scalar/aggregate/call/probe/SIMD matrix,
optional and pair-bearing instruction paths, and every terminator operand
shape.  The matrix is bootstrap-runtime diagnostic evidence only.  This change
does not re-enable optimizer-engine DCE or claim a production coverage runtime.
