# Flat AST do-block bridge

Executable source: `test/01_unit/compiler/frontend/flat_ast_do_block_bridge_spec.spl`.
Requirement: REQ-COMPILER-FRONTEND-001.

The flat parser emits EXPR_DO_BLOCK for both `do:` and `ce NAME:`. Its STMTS
must become an ExprKind.Block with the same ordered statements and final
expression. The bridge and shared branch helper both recognize this tag.

| Scenario | Real assertion |
| --- | --- |
| Empty do block | Block with zero statements and no parser error |
| Single expression | Integer 37 remains the sole statement |
| Nested block | Outer 11 remains first; inner block retains 29 |
| Ordinary block compatibility | Separate LEFT tail 19 follows statement 5 |
| Parsed do/ce | Actual parser produces ordered [7,43] and [13,47] bodies |

Run `bin/simple test test/01_unit/compiler/frontend/flat_ast_do_block_bridge_spec.spl`.

Execution status: **NOT RUN**. This manual describes authored assertions;
it is not runtime qualification or evidence of a passing compiler producer.
The combined bug `parser_nested_block_do_import_typed_var_gaps_2026_11_07`
also records dynamic-array no-initializer policy and lexical-import behavior,
which remain outside this narrow do-block conversion repair.
