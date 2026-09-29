# Canonical Simple parser diagnostic and recovery effect inventory

**Status:** source-level call-site index for the canonical scalar Simple grammar/action handoff. It is not a candidate execution or parity receipt.

**Source baseline:** `origin/main` at `15d989519be3d4b9b9aeaa3eb627b6bff874110b`. Paths below are relative to `src/compiler/10.frontend/core/`. This index excludes tests and imports. Nine raw text matches are definitions or comments, leaving 424 calls. The scanner records direct calls in source lines; dynamic effects and indirect callers still need review.

**Direct call sites:** 424 across 90 containing functions: 129 `parser_error`, 14 `parser_warn`, and 281 `parser_expect`.

## Central semantics

- `parser_expect` consumes only on a match. On mismatch it records a path-qualified error, sets the parser error flag and mirror, saves the first error if empty, and leaves the unexpected token in place.
- `parser_error` records a line/column message, sets the same error state and first-error mirror, and does not advance the token itself. It prints path/token context separately when diagnostics are enabled.
- Diagnostic suppression hides printed errors; both functions still record the error. `parser_warn` appends to a separate warning list and prints only under compiler trace.
- Reset replaces error/warning arrays and clears state; append preserves the arrays but clears the current error flag. Isolated parse restores the prior flag through the frontend wrapper. These state transitions are part of differential parity.

## Direct call-site index

Each row is a containing source function, with line numbers for direct calls. An empty cell means no direct call of that kind. These are extraction anchors, not stable program IDs.

| Source | Function | Error lines | Warning lines | Expect lines |
|---|---|---:|---:|---:|
| `_ParserDecls/bitfield_aop_arch_decls.spl` | `parse_bitfield_decl` | 101, 152, 167, 177 | — | 81, 95, 98, 110, 112, 146, 147 |
| `_ParserDecls/bitfield_aop_arch_decls.spl` | `parse_pointcut_text` | 194, 197, 204 | — | 199 |
| `_ParserDecls/bitfield_aop_arch_decls.spl` | `parse_aop_advice_decl` | — | — | 228, 230, 232 |
| `_ParserDecls/enum_module_body.spl` | `parse_layer_decl` | 134, 143 | — | — |
| `_ParserDecls/enum_module_body.spl` | `parser_sffi_record_key` | 192 | — | — |
| `_ParserDecls/enum_module_body.spl` | `parse_sffi_arg_value` | 219 | — | — |
| `_ParserDecls/enum_module_body.spl` | `parse_resource_decl` | 240, 245, 247 | — | — |
| `_ParserDecls/enum_module_body.spl` | `parse_enum_decl` | 376 | — | 269, 291, 293, 333, 339, 380, 431 |
| `_ParserDecls/enum_module_body.spl` | `parse_top_level_visibility` | — | 498 | 488 |
| `_ParserDecls/enum_module_body.spl` | `parse_mod_decl_with_visibility` | 520 | — | — |
| `_ParserDecls/enum_module_body.spl` | `parse_module_decl_with_visibility` | 534, 588 | — | 566, 571 |
| `_ParserDecls/enum_module_body.spl` | `parser_parse_member_attribute` | 659 | — | — |
| `_ParserDecls/enum_module_body.spl` | `parse_module_body` | 939, 981, 1318, 1322, 1396, 1417, 1439, 1489, 1501, 1531, 1614, 1644, 1678 | 1503 | 1021, 1026, 1094, 1099, 1355, 1672, 1673, 1680, 1697, 1698 |
| `_ParserDecls/extend_decls.spl` | `parse_extend_constructor` | 98, 104, 108 | — | 137 |
| `_ParserDecls/extend_decls.spl` | `parse_extend_section` | — | — | 167 |
| `_ParserDecls/extend_decls.spl` | `parse_extend_enum_decl` | 201, 208, 229, 233 | — | 205 |
| `_ParserDecls/fn_struct_decls.spl` | `parser_expect_param_name` | 128 | — | — |
| `_ParserDecls/fn_struct_decls.spl` | `parse_raw_domain_block_payload` | 276 | — | — |
| `_ParserDecls/fn_struct_decls.spl` | `parse_module_domain_block_decl` | 299 | — | 290 |
| `_ParserDecls/fn_struct_decls.spl` | `parse_type_param_constraint_list` | — | — | 368 |
| `_ParserDecls/fn_struct_decls.spl` | `parse_type_params` | 399 | — | 430, 432 |
| `_ParserDecls/fn_struct_decls.spl` | `parser_skip_fn_where_clause` | 525, 531, 541, 550, 554, 574 | — | — |
| `_ParserDecls/fn_struct_decls.spl` | `parse_fn_decl` | — | — | 583, 642 |
| `_ParserDecls/fn_struct_decls.spl` | `parse_extern_fn_decl` | — | — | 678, 681, 688, 718 |
| `_ParserDecls/fn_struct_decls.spl` | `parse_struct_or_trait_decl` | 947, 1037, 1072, 1082, 1085, 1099 | — | 868, 884, 889, 892, 893, 895, 942, 948, 1045, 1077, 1083 |
| `_ParserPrimary/asm_match_suffix.spl` | `parse_asm_target_spec` | 73, 77, 114, 125, 133, 141, 146 | — | 59, 149 |
| `_ParserPrimary/asm_match_suffix.spl` | `parse_asm_match` | 174, 189 | — | 198, 208, 213, 243, 253, 258 |
| `_ParserPrimary/asm_raw_parsing.spl` | `parse_optional_rationale_args` | — | — | 79 |
| `_ParserPrimary/asm_raw_parsing.spl` | `parse_raw_braced_payload` | 142 | — | — |
| `_ParserPrimary/asm_raw_parsing.spl` | `parse_legacy_parenthesized_asm` | 192 | 152 | 153, 173, 180, 197, 200, 213 |
| `_ParserPrimary/primary_expr.spl` | `parse_fn_lambda_after_kw` | — | — | 122, 145, 156 |
| `_ParserPrimary/primary_expr.spl` | `parse_primary_expr` | 347, 367, 382, 403, 462, 467, 472, 513, 794, 837, 874, 1023, 1095, 1107 | 357, 363, 496, 763, 770, 777 | 286, 309, 311, 324, 341, 351, 567, 579, 589, 590, 625, 643, 670, 671, 677, 679, 687, 697, 698, 704, 729, 851, 888, 956, 957, 963, 965, 967, 969, 970, 975, 986, 987, 993, 1029, 1096 |
| `parser.spl` | `parser_guarded_int_text` | 443, 457 | — | — |
| `parser.spl` | `parser_warn_print_if_needed` | — | 492 | — |
| `parser.spl` | `parser_parse_type_impl` | 599, 616, 634, 644, 692, 810, 822, 1059, 1068, 1082 | — | 780, 783, 971, 1006, 1016, 1041, 1080 |
| `parser.spl` | `parser_parse_type_with_union` | 1101 | — | — |
| `parser_asm.spl` | `parse_asm_target_spec` | 39, 43, 80, 91, 99, 107, 112 | — | 25, 115 |
| `parser_asm.spl` | `parse_asm_match` | 140, 155 | — | 164, 174, 179, 209, 219, 224 |
| `parser_cli.spl` | `parse_cli_decl` | — | — | 42, 43, 45, 80, 82, 83, 109, 111, 119, 129, 130, 132, 141, 152, 159, 166 |
| `parser_cli.spl` | `parse_cli_option_value` | 247 | — | 231 |
| `parser_cli.spl` | `parse_cli_subcommand` | — | — | 256, 289, 291, 292, 309 |
| `parser_decls_fn.spl` | `parse_type_param_constraint_list` | — | — | 49 |
| `parser_decls_fn.spl` | `parse_type_params` | 80 | — | 108, 110 |
| `parser_decls_fn.spl` | `parse_fn_decl` | — | — | 119, 124, 157, 177 |
| `parser_decls_fn.spl` | `parse_extern_fn_decl` | — | — | 184, 186, 191, 221 |
| `parser_decls_types.spl` | `parse_enum_decl` | — | — | 65, 70, 72, 135, 186 |
| `parser_decls_types.spl` | `parse_bitfield_decl` | 229, 270, 276, 285 | — | 216, 223, 225, 231, 233, 264, 265 |
| `parser_decls_use.spl` | `take_export_identifier` | — | — | 83 |
| `parser_decls_use.spl` | `parse_use_decl` | — | — | 178 |
| `parser_decls_use.spl` | `parse_export_decl` | 322 | — | 298, 324, 372, 401 |
| `parser_decls_use.spl` | `parse_val_decl` | — | — | 457, 477, 484 |
| `parser_decls_use.spl` | `parse_lazy_val_decl` | — | — | 495, 502 |
| `parser_decls_use.spl` | `parse_var_decl` | — | — | 513, 520 |
| `parser_decls_use.spl` | `parse_class_body_method` | — | — | 553, 560, 612 |
| `parser_decls_use.spl` | `skip_impl_where_clause` | 703, 719 | — | — |
| `parser_decls_use.spl` | `parse_impl_decl` | — | — | 780, 782 |
| `parser_decls_use.spl` | `parse_ce_decl` | — | — | 832, 833 |
| `parser_expr.spl` | `parse_expr` | 110 | — | — |
| `parser_expr.spl` | `validate_bracket_expr` | 142 | — | — |
| `parser_expr.spl` | `parse_assignment` | 210 | — | — |
| `parser_expr.spl` | `try_skip_ident_generic_args` | 909 | — | — |
| `parser_expr.spl` | `parse_struct_lit_tail` | 979, 986 | — | 991 |
| `parser_expr.spl` | `parse_postfix_on` | 1105 | — | 1133, 1150, 1167, 1171, 1197, 1206 |
| `parser_expr.spl` | `parse_postfix` | 1313 | — | 1359, 1377, 1396, 1400, 1429, 1441 |
| `parser_stmts.spl` | `parse_optional_rationale_args` | — | — | 118 |
| `parser_stmts.spl` | `parse_trailing_colon_block_arg` | — | — | 250 |
| `parser_stmts.spl` | `parse_block` | — | — | 347 |
| `parser_stmts.spl` | `parse_extern_fn_stmt_inline` | — | — | 406, 408, 409, 425 |
| `parser_stmts.spl` | `parse_contract_clause_body` | — | — | 447, 454 |
| `parser_stmts.spl` | `parse_statement` | 726 | 808, 819, 830, 847 | 656, 1047 |
| `parser_stmts.spl` | `parse_refutable_val_else_stmt` | 1120, 1127, 1132 | — | 1104, 1111, 1114, 1123 |
| `parser_stmts.spl` | `parse_val_decl_stmt` | 1160 | — | 1175, 1183, 1197 |
| `parser_stmts.spl` | `parse_lazy_val_decl_stmt` | — | — | 1209, 1216 |
| `parser_stmts.spl` | `parse_var_decl_stmt` | — | — | 1242, 1250, 1291 |
| `parser_stmts.spl` | `var_no_init_default_expr` | 1322 | — | — |
| `parser_stmts.spl` | `parse_if_stmt` | 1367 | — | 1368, 1370, 1387, 1407 |
| `parser_stmts.spl` | `parse_for_binding_name` | — | — | 1487, 1494 |
| `parser_stmts.spl` | `parse_for_stmt` | — | — | 1518, 1531, 1533 |
| `parser_stmts.spl` | `parse_static_for_stmt` | — | — | 1540, 1541, 1543 |
| `parser_stmts.spl` | `parse_while_stmt` | 1562 | — | 1563, 1565, 1612 |
| `parser_stmts.spl` | `parse_loop_stmt` | — | — | 1622 |
| `parser_stmts.spl` | `parse_match_arms_common` | — | — | 1706, 1709, 1873, 1876, 1910, 1956 |
| `parser_stmts.spl` | `parse_receive_stmt` | 2084 | — | 1990, 1992, 2040, 2074 |
| `parser_stmts.spl` | `parse_bind_stmt` | — | — | 2092, 2093 |
| `parser_stmts.spl` | `parse_if_expr` | 2133 | — | 2134, 2136, 2150, 2158, 2188 |
| `parser_stmts.spl` | `parse_for_expr` | — | — | 2264, 2265, 2267 |
| `parser_stmts.spl` | `parse_while_expr` | — | — | 2277 |
| `parser_stmts.spl` | `parse_tuple_destructure_val` | — | — | 2310, 2318, 2326, 2334, 2335, 2337 |
| `parser_stmts.spl` | `parse_tuple_destructure_var` | — | — | 2353, 2361, 2369, 2377, 2378, 2380 |
| `parser_stmts.spl` | `parse_gpu_launch_stmt` | — | — | 2397, 2409, 2410, 2413, 2425, 2432, 2433 |

## Recovery edges checked by hand

- `parser_decls_use.spl:300-324`: export-list recovery reports an unexpected separator, consumes one token, then continues until `}` or EOF. The closing `parser_expect` may report without consuming.
- `parser_stmts.spl:315-352`: an indented block stops on DEDENT (consumed) or EOF (left in place); a bodyless same-column form emits an expected-INDENT error and returns an empty body.
- `parser_decls_use.spl:691-719`: impl-header `where` recovery consumes each non-EOF token until the separating colon or EOF; EOF emits an unterminated-clause error without consuming.

## Retained oracle assertions

`test/01_unit/compiler/frontend/parser_diagnostic_recovery_oracle_spec.spl`
pins three central effects: failed `parser_expect` preserves the current token
while recording one path-qualified error; suppression preserves that error
without incrementing the print count; and a new reset clears the recorded
error sequence. Existing
`test/01_unit/compiler/frontend/lexer_dead_stream_forward_progress_spec.spl`
covers bounded module-level recovery, while
`test/01_unit/compiler/frontend/flat_ast_speculative_diagnostics_spec.spl`
checks that recovered interpolation speculation does not publish diagnostics.
These focused assertions do not cover the 424 indexed branches, append-mode
ordering, or candidate parity. Source-matched execution is still required.

## Remaining admission work

Classify the exact recovery edge and token progress for every indexed call site, then inventory indirect diagnostics, lexical errors, post-parse transform diagnostics, AST/module effects, and rollback journals. The action-program validator must reject nonprogress cycles and exposed effects before a rollback point. No opcode number or provider admission follows from this index alone.
