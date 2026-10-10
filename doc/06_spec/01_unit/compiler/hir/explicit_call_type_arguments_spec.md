# Explicit direct-call type arguments

Executable: `test/01_unit/compiler/hir/explicit_call_type_arguments_spec.spl`.

The scenario parses and lowers a return-only generic call `absent<i64>()`
through the real frontend/HIR owner. It requires a call with no value arguments
and exactly one signed 64-bit integer type argument, a present function body
and no lowering errors. It contains no placeholder passes.

Status: authored, not executed through a qualified spec runner. Native fixtures
cover return-only integer/text calls with a comparison control and invalid
explicit type-argument arity. Their native verification is pending.
