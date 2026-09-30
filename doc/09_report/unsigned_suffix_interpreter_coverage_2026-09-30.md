# Unsigned suffix interpreter frontend coverage

**Status: UNEXECUTED.** Source review on 2026-09-30 against freshly fetched
`origin/main` at `fd82119d9c911b2cecaa66d95d16930792a40953`. No build, test,
interpreter invocation, reproducer or docgen was run for this change. Normal
repository commit/push checks are separate from runtime qualification.

## Root cause and route

The unsigned suffix parser fix is already landed through PR #2096. Older
Linux and Windows producers rejected `18446744073709551615u64` through the
signed decimal limit; this coverage change introduces no production fix.

`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` selects
`parse_unsigned_int_literal_text` for u8/u16/u32/u64, then creates the suffix
AST node. The helper compares the declared width before constructing the i64
bit carrier. A u64 maximum has carrier word -1, not a negative source literal.

The CLI in-process route calls `interpret_file` in
`src/compiler/80.driver/driver_api_interpret.spl`, selects
`CompileMode.Interpret`, and runs the shared frontend/HIR before
`InterpreterBackendImpl`. A cached SMF can bypass source parsing; eventual
runtime evidence must identify which route actually executed.

The separate core interpreter module route calls `core_frontend_parse_reset`.
Its expression entrypoint `core_interpret_expr` calls `parse_expr` directly.
Both reach the same suffix decoder. A parse error makes the expression
entrypoint return -1 and set `parse error` before evaluation.

The older Tree-sitter app wrapper and the existing UInt-to-text regression
exercise different paths or causes and cannot establish this parser parity.

## Existing and added assertions

Existing coverage:
`test/01_unit/compiler/frontend/unsigned_integer_literal_suffix_spec.spl`.

| Boundary | Existing production-decoder assertions | Added coverage |
|---|---|---|
| Decimal max/max+1 | u8, u16, u32, u64 | All four overflows through core interpreter entrypoint |
| Hexadecimal max/max+1 | u8, u64 | u16/u32 decoder; all four interpreter overflow paths |
| Binary max/max+1 | u8 | u16/u32/u64 decoder; all four interpreter overflow paths |
| Octal max/max+1 | u64 | u8/u16/u32 decoder; all four interpreter overflow paths |
| Signed control | i64 bounds through decoder | Actual unsuffixed i64-max evaluation and signed overflow rejection |

The new spec is
`test/01_unit/compiler/interpreter/unsigned_suffix_frontend_spec.spl`.
Five scenarios cover sixteen radix/width pairs plus a signed control.
For each pair the helper checks the production decoder's exact maximum word,
then requires both the interpreter's rejection result and the specific
unsigned-width parser diagnostic for max+1. An unrelated evaluator error
cannot satisfy those negative assertions. The helper leaves diagnostic
suppression settings untouched.

Existing high-bit transitions, separators, leading zeroes, malformed-token
precedence, primary bridge Cast/payload assertions and the separate typed
dynlib constant follow-up are not duplicated. The decoder supports only
u8/u16/u32/u64; no usize/u128 support is claimed. Binary cases test the first
extra bit; octal cases include widths not divisible by three. Allocation or
platform pointer sizes do not affect this decoder root.

## Evidence limits

Accepted unsigned values in this spec are **decoder evidence**, not positive
interpreter execution evidence. Source inspection found that the core AST
evaluator's `eval_expr` lacks `EXPR_SUFFIXED_LIT` dispatch after the parser
creates that node. This downstream surface is separate from the signed-limit
parser root and was neither executed nor changed here. The HIR interpreter
instead receives suffixes through the existing primary bridge. Complete
positive interpreter suffix execution remains unqualified.

The task authorized source-only coverage and prohibited new runtime cycles.
Consequently docgen also remains unexecuted: there is no generated manual,
zero-stub result, parser runtime PASS or interpreter parity PASS. Future
qualification requires an admitted source-matched pure-Simple runner and an
authorized verification cycle; a seed run cannot substitute for that evidence.
