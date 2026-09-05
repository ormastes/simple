# MethodCallStatic declared-default metadata gap

Status: open; bootstrap call site safely mitigated

## Symptom

During the packed-memory Stage3 build, the call
`self.lower_runtime_module_initializers(module, const_vals)` resolved to an
instance method whose ABI has four parameters: receiver, module, consts, and
`bootstrap_module_index: i64 = -1`. The Rust Cranelift boundary correctly
preserved the receiver, then observed only three supplied MIR operands.

Generic codegen padding is not a correct repair. Padding the final slot with
tagged nil or zero changes the declared value `-1` and therefore changes module
initializer identity.

## Root cause

Pure-Simple MIR has default-expression lookup and lowering in
`pad_trailing_default_args`, but this cross-module MethodCallStatic path did not
carry or recover the callee's declared default before reaching codegen. MIR
therefore lacks the semantic operand; Cranelift signatures carry types and
arity, not default expressions.

## Current mitigation

The bootstrap-critical call in
`src/compiler/50.mir/_MirLowering/module_lowering.spl` passes `-1` explicitly.
The Cranelift receiver fix remains strict and refuses an arity mismatch instead
of inventing a value.

## Required general fix

Extend owner-qualified cross-module default metadata through HIR/MIR call
resolution. Before emitting MethodCallStatic, lower every omitted trailing
declared default expression at the caller and append its operand. Do not encode
defaults in backend signatures and do not use nil/zero padding as semantics.

Acceptance regression: an imported instance method with a non-nil/non-zero
default (for example `offset: i64 = -7`) must return or otherwise observe `-7`
when omitted, in interpreter and native execution. An adjacent explicit value
must remain unchanged, and a free call must not acquire an implicit receiver.

