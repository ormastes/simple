# Flat AST do-block bridge

Executable source: `test/01_unit/compiler/frontend/flat_ast_do_block_bridge_spec.spl`.
Requirement: REQ-COMPILER-FRONTEND-001.

The flat parser emits EXPR_DO_BLOCK for `do:`. Its STMTS become an ExprKind.Block
with the same ordered statements. Only ordinary EXPR_BLOCK reads a separate LEFT
tail. `ce NAME:` keeps its builder identity in S and remains a loud bridge-only unsupported
error. Shared core parsing still succeeds; this patch does not accept a plain
block as computation-builder execution.

| Scenario | Authored real assertion |
| --- | --- |
| Empty do block | Block with zero statements and no parser error |
| Single expression | Integer 37 remains the sole statement |
| Nested block | Outer 11 remains first; inner block retains 29 |
| Ordinary compatibility | Separate LEFT tail 19 follows statement 5 |
| Parsed do | Real parser retains ordered [7,43] |
| Expression-if callers | Both branches retain [17] and [31] |
| Lambda caller | Do body retains 53 |
| HIR tail extraction | Typed function's nested HirBlock has value 43 |
| CE owner compatibility | Shared parse succeeds, S keeps builder, bridge rejects |

The existing unsupported-expression spec now uses a genuinely unknown tag 9999,
checks bridge-only `ce builder` rejection, checks a parsed unsupported atom,
and protects supported calls.

Run the two specs with an admitted self-hosted runner. Execution: **NOT RUN**.
This manual describes authored assertions, not evidence of runtime qualification.
The combined bug also records dynamic-array no-initializer policy and lexical
import behavior; both remain outside this narrow conversion repair.
