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
two `StoreGlobal` instructions return to declaration order. Equal synthetic
spans exercise the symbol-ID tie-break. Current-source native execution
awaits the next incremental self-hosted compiler candidate.

The shared cross-target fixture repeats the dependent `4 -> 5 -> 45` startup
oracle. Existing schedulers execute it with LLVM and Cranelift on FreeBSD,
AArch64, and RV64, and require target objects on ARM32, RV32, and Windows ARM64;
the hosted Linux/macOS/Windows strict-dual case inherits the same source.
