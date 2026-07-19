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

The same owner formerly selected only initializers whose HIR root was exactly
`Call`, silently dropping wrapped calls such as `init_value() * 2` and the
production RISC-V `contract().pointer_bits / 8` word-size bindings. MIR now
runtime-initializes wrapped expressions for backend-supported scalar bindings,
while the four literal kinds remain compile-time constants. Existing root-call
behavior remains unchanged for compatibility; unsupported nil and aggregate
shapes are not newly materialized as Cranelift statics. The affected RISC-V
contract-derived globals now declare their scalar type explicitly because HIR
keeps unannotated nonliteral module bindings as `Infer`.

## Regression

`native_module_global_initializer.spl` initializes `module_value`, then derives
`next_value` from it, checks a wrapped-call global, and returns `45`. The hosted
LLVM/Cranelift matrix and the
scoped FreeBSD Cranelift gate consume that fixture; the Pure MIR unit feeds the
shared ordering helper an explicitly reversed constant array, then checks the
three `StoreGlobal` instructions return to declaration order and the wrapped
global is read through `LoadGlobal`. Equal synthetic
spans exercise the symbol-ID tie-break. Current-source native execution
awaits the next incremental self-hosted compiler candidate.

## Interpolated string globals

`lower_const_expr` formerly folded every `StringLit`, including a literal with
runtime interpolations. MIR now keeps plain literals constant but gives an
interpolated module binding a nil-backed raw-text pointer static and evaluates
it in the existing ordered initializer. Cranelift admits only `Opaque("str")`
runtime statics, not tuple-backed strings or other opaque types. Its literal
segments reuse the existing tagged-or-raw `rt_interp_cstr` normalization before
raw concatenation, so the pointer stored globally has the same representation
on LLVM and Cranelift. The shared native fixture checks `value=7` on the hosted,
FreeBSD, AArch64, and RISC-V64 execution lanes; ARM32, RISC-V32, and Windows
ARM64 retain their object gates.

The shared cross-target fixture repeats the dependent `4 -> 5 -> 45` startup
oracle. Existing schedulers execute it with LLVM and Cranelift on FreeBSD,
AArch64, and RV64, and require target objects on ARM32, RV32, and Windows ARM64;
the hosted Linux/macOS/Windows strict-dual case inherits the same source.
