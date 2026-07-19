# Multiple dynamic module globals lost declaration order

- **ID:** native_multiple_module_initializers_declaration_order_2026-07-19
- **Status:** SOURCE FIXED (rebuilt native execution pending)
- **Severity:** high (dependent globals could not compile)
- **Owner:** shared Pure Simple MIR lowering

## Root cause and fix

`HirModule.constants` is a dictionary, so MIR lowering rejected more than one
call-initialized global instead of risking unordered startup. The flat binding
parser and bridge also replaced every declaration location with a zero span.
The Pure frontend now carries binding token positions into `HirConst.span`, and
the shared initializer owner sorts dynamic constants by `span.start` (with
`symbol.id` as the synthetic-span tie-break) before emitting its existing
sequential stores.

## Regression

`native_module_global_initializer.spl` initializes `module_value`, then derives
`next_value` from it and returns `45`. The hosted LLVM/Cranelift matrix and the
scoped FreeBSD Cranelift gate consume that fixture; the Pure MIR unit feeds the
shared ordering helper an explicitly reversed constant array, then checks the
two `StoreGlobal` instructions return to declaration order. Current-source native execution
awaits the next incremental self-hosted compiler candidate.
