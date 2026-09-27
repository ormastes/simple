# Canonical Simple parser rule candidate survey

**Status:** mechanical source survey on `origin/main` at `15d989519be3d4b9b9aeaa3eb627b6bff874110b`; companion to the checkpoint/effect inventory and draft design PR #1706. This is a rule extraction queue, not an executable grammar program or parity receipt.

The table lists every top-level function named `parse_*`, `try_parse_*`, `_parse_*`, `parser_parse_*`, or `parser_try_*` in the lexer/parser file set and interpolation/placeholder transform. A direct marker is emitted only when a matching call occurs after that function header and before the next top-level declaration. Calls inside helpers and indirect effects are **not** propagated. `none detected` does not mean pure. This name-based filter can omit grammar helpers with other names and include non-rule utilities; every row needs semantic review before it becomes a stable program entry or an explicit unsupported reason.

**Survey size:** 133 candidate functions in 18 files. Direct marker counts: AST/module call 83, checkpoint 10, diagnostic 80, lexer mode 3, none detected 25, raw cursor 2.

Source paths in the table are relative to `src/compiler/10.frontend/core/`.

| Source | Function | Direct markers |
|---|---|---|
| `../desugar/placeholder_lambda.spl:117` | `parse_placeholder_number` | none detected |
| `_ParserDecls/bitfield_aop_arch_decls.spl:77` | `parse_bitfield_decl` | diagnostic, AST/module call |
| `_ParserDecls/bitfield_aop_arch_decls.spl:188` | `parse_pointcut_text` | diagnostic |
| `_ParserDecls/bitfield_aop_arch_decls.spl:224` | `parse_aop_advice_decl` | diagnostic, AST/module call |
| `_ParserDecls/bitfield_aop_arch_decls.spl:242` | `parse_arch_rule_decl` | AST/module call |
| `_ParserDecls/enum_module_body.spl:130` | `parse_layer_decl` | diagnostic, AST/module call |
| `_ParserDecls/enum_module_body.spl:209` | `parse_sffi_arg_value` | diagnostic |
| `_ParserDecls/enum_module_body.spl:236` | `parse_resource_decl` | diagnostic, AST/module call |
| `_ParserDecls/enum_module_body.spl:266` | `parse_enum_decl` | diagnostic, AST/module call |
| `_ParserDecls/enum_module_body.spl:479` | `parse_top_level_visibility` | diagnostic |
| `_ParserDecls/enum_module_body.spl:510` | `parse_mod_decl_with_visibility` | diagnostic, AST/module call |
| `_ParserDecls/enum_module_body.spl:529` | `parse_module_decl_with_visibility` | diagnostic, AST/module call |
| `_ParserDecls/enum_module_body.spl:637` | `parser_parse_member_attribute` | diagnostic |
| `_ParserDecls/enum_module_body.spl:865` | `parse_enum_open_section_body` | none detected |
| `_ParserDecls/enum_module_body.spl:896` | `parse_module_body` | diagnostic, AST/module call |
| `_ParserDecls/extend_decls.spl:92` | `parse_extend_constructor` | diagnostic |
| `_ParserDecls/extend_decls.spl:166` | `parse_extend_section` | diagnostic |
| `_ParserDecls/extend_decls.spl:198` | `parse_extend_enum_decl` | diagnostic |
| `_ParserDecls/fn_struct_decls.spl:218` | `parse_raw_domain_block_advance_lexer` | raw cursor |
| `_ParserDecls/fn_struct_decls.spl:242` | `parse_raw_domain_block_payload` | diagnostic |
| `_ParserDecls/fn_struct_decls.spl:282` | `parse_module_domain_block_decl` | diagnostic, AST/module call |
| `_ParserDecls/fn_struct_decls.spl:323` | `parse_type_param_constraint_list` | diagnostic |
| `_ParserDecls/fn_struct_decls.spl:371` | `parse_type_params` | diagnostic |
| `_ParserDecls/fn_struct_decls.spl:488` | `parser_try_skip_signature_layout_before_colon` | checkpoint |
| `_ParserDecls/fn_struct_decls.spl:576` | `parse_fn_decl` | diagnostic, AST/module call |
| `_ParserDecls/fn_struct_decls.spl:673` | `parse_extern_fn_decl` | diagnostic, AST/module call |
| `_ParserDecls/fn_struct_decls.spl:862` | `parse_struct_decl` | none detected |
| `_ParserDecls/fn_struct_decls.spl:865` | `parse_struct_or_trait_decl` | checkpoint, diagnostic, AST/module call |
| `_ParserPrimary/asm_match_suffix.spl:55` | `parse_asm_target_spec` | diagnostic |
| `_ParserPrimary/asm_match_suffix.spl:155` | `parse_int_text` | none detected |
| `_ParserPrimary/asm_match_suffix.spl:164` | `parse_asm_match` | diagnostic, AST/module call |
| `_ParserPrimary/asm_match_suffix.spl:288` | `parse_asm_assert_expr` | AST/module call |
| `_ParserPrimary/asm_raw_parsing.spl:62` | `parse_optional_rationale_args` | diagnostic |
| `_ParserPrimary/asm_raw_parsing.spl:82` | `parse_raw_asm_normalize` | none detected |
| `_ParserPrimary/asm_raw_parsing.spl:97` | `parse_raw_asm_advance_lexer` | raw cursor |
| `_ParserPrimary/asm_raw_parsing.spl:111` | `parse_raw_braced_payload` | diagnostic |
| `_ParserPrimary/asm_raw_parsing.spl:148` | `parse_raw_asm_braced_payload` | none detected |
| `_ParserPrimary/asm_raw_parsing.spl:151` | `parse_legacy_parenthesized_asm` | diagnostic, AST/module call |
| `_ParserPrimary/primary_expr.spl:120` | `parse_fn_lambda_after_kw` | lexer mode, diagnostic, AST/module call |
| `_ParserPrimary/primary_expr.spl:192` | `parse_int_literal_text` | none detected |
| `_ParserPrimary/primary_expr.spl:254` | `parse_primary_expr` | lexer mode, diagnostic, AST/module call |
| `_ParserStmt/match_type_pattern.spl:73` | `parse_match_type_pattern` | AST/module call |
| `parser.spl:568` | `parser_parse_type` | none detected |
| `parser.spl:571` | `parser_parse_cast_type` | none detected |
| `parser.spl:577` | `parser_parse_tuple_element_type` | none detected |
| `parser.spl:584` | `parser_parse_type_impl` | diagnostic |
| `parser.spl:1086` | `parser_parse_type_with_union` | diagnostic |
| `parser.spl:1107` | `_parse_module_with_diagnostics` | none detected |
| `parser.spl:1132` | `parse_module` | none detected |
| `parser.spl:1135` | `parse_module_silent` | none detected |
| `parser.spl:1145` | `parse_module_silent_checked` | none detected |
| `parser.spl:1150` | `parse_module_file` | none detected |
| `parser_asm.spl:21` | `parse_asm_target_spec` | diagnostic |
| `parser_asm.spl:121` | `parse_int_text` | none detected |
| `parser_asm.spl:130` | `parse_asm_match` | diagnostic, AST/module call |
| `parser_asm.spl:254` | `parse_asm_assert_expr` | AST/module call |
| `parser_cli.spl:36` | `parse_cli_decl` | diagnostic, AST/module call |
| `parser_cli.spl:200` | `parse_cli_option_value` | diagnostic, AST/module call |
| `parser_cli.spl:253` | `parse_cli_subcommand` | diagnostic, AST/module call |
| `parser_decls_fn.spl:26` | `parse_type_param_constraint_list` | diagnostic |
| `parser_decls_fn.spl:52` | `parse_type_params` | diagnostic |
| `parser_decls_fn.spl:116` | `parse_fn_decl` | diagnostic, AST/module call |
| `parser_decls_fn.spl:182` | `parse_extern_fn_decl` | diagnostic, AST/module call |
| `parser_decls_types.spl:62` | `parse_enum_decl` | diagnostic, AST/module call |
| `parser_decls_types.spl:212` | `parse_bitfield_decl` | diagnostic, AST/module call |
| `parser_decls_use.spl:55` | `parse_prof_now` | none detected |
| `parser_decls_use.spl:60` | `parse_prof_mark` | none detected |
| `parser_decls_use.spl:88` | `parse_export_source_module` | none detected |
| `parser_decls_use.spl:111` | `parse_use_decl` | diagnostic, AST/module call |
| `parser_decls_use.spl:291` | `parse_export_decl` | diagnostic, AST/module call |
| `parser_decls_use.spl:445` | `parse_val_decl` | diagnostic, AST/module call |
| `parser_decls_use.spl:489` | `parse_lazy_val_decl` | diagnostic, AST/module call |
| `parser_decls_use.spl:507` | `parse_var_decl` | diagnostic, AST/module call |
| `parser_decls_use.spl:527` | `parse_class_body_method` | diagnostic, AST/module call |
| `parser_decls_use.spl:738` | `parse_impl_target_type` | none detected |
| `parser_decls_use.spl:760` | `parse_impl_decl` | diagnostic, AST/module call |
| `parser_decls_use.spl:829` | `parse_ce_decl` | diagnostic, AST/module call |
| `parser_expr.spl:105` | `parse_expr` | diagnostic, AST/module call |
| `parser_expr.spl:146` | `parse_pipe` | AST/module call |
| `parser_expr.spl:186` | `parse_compose` | AST/module call |
| `parser_expr.spl:203` | `parse_assignment` | diagnostic, AST/module call |
| `parser_expr.spl:239` | `parse_or` | AST/module call |
| `parser_expr.spl:261` | `parse_and` | AST/module call |
| `parser_expr.spl:283` | `parse_not` | AST/module call |
| `parser_expr.spl:294` | `parse_comparison` | checkpoint, AST/module call |
| `parser_expr.spl:365` | `parse_null_coalesce` | AST/module call |
| `parser_expr.spl:377` | `parse_range` | AST/module call |
| `parser_expr.spl:399` | `parse_addition` | AST/module call |
| `parser_expr.spl:415` | `parse_multiplication` | AST/module call |
| `parser_expr.spl:451` | `parse_unary` | AST/module call |
| `parser_expr.spl:491` | `parse_binary_from` | checkpoint, AST/module call |
| `parser_expr.spl:681` | `parse_call_arg` | none detected |
| `parser_expr.spl:693` | `parse_call_arg_raw` | checkpoint, AST/module call |
| `parser_expr.spl:961` | `parse_struct_lit_tail` | diagnostic, AST/module call |
| `parser_expr.spl:1035` | `parse_postfix_on` | diagnostic, AST/module call |
| `parser_expr.spl:1243` | `parse_postfix` | diagnostic, AST/module call |
| `parser_stmts.spl:101` | `parse_optional_rationale_args` | diagnostic |
| `parser_stmts.spl:229` | `try_parse_bare_ident_string_call` | checkpoint, AST/module call |
| `parser_stmts.spl:249` | `parse_trailing_colon_block_arg` | diagnostic, AST/module call |
| `parser_stmts.spl:273` | `parse_block_flat_body_can_start` | none detected |
| `parser_stmts.spl:315` | `parse_block` | diagnostic |
| `parser_stmts.spl:358` | `parse_use_stmt_inline` | AST/module call |
| `parser_stmts.spl:404` | `parse_extern_fn_stmt_inline` | diagnostic, AST/module call |
| `parser_stmts.spl:434` | `parse_contract_clause_expr_stmt` | AST/module call |
| `parser_stmts.spl:443` | `parse_contract_clause_body` | diagnostic |
| `parser_stmts.spl:459` | `try_parse_contract_stmt` | checkpoint, AST/module call |
| `parser_stmts.spl:528` | `parse_unsafe_block_expr_if_present` | checkpoint, AST/module call |
| `parser_stmts.spl:613` | `parse_statement` | checkpoint, diagnostic, AST/module call |
| `parser_stmts.spl:1095` | `parse_refutable_val_else_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1145` | `parse_val_decl_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1206` | `parse_lazy_val_decl_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1224` | `parse_var_decl_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1338` | `parse_if_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1464` | `parse_for_binding_name` | checkpoint, diagnostic |
| `parser_stmts.spl:1507` | `parse_for_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1537` | `parse_static_for_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1547` | `parse_while_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1620` | `parse_loop_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:1659` | `parse_match_region_marker` | AST/module call |
| `parser_stmts.spl:1695` | `parse_match_arms_common` | lexer mode, diagnostic, AST/module call |
| `parser_stmts.spl:1970` | `parse_match_stmt_tail` | AST/module call |
| `parser_stmts.spl:1984` | `parse_match_expr_tail` | AST/module call |
| `parser_stmts.spl:1988` | `parse_receive_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:2089` | `parse_bind_stmt` | diagnostic, AST/module call |
| `parser_stmts.spl:2099` | `parse_if_expr` | diagnostic, AST/module call |
| `parser_stmts.spl:2261` | `parse_for_expr` | diagnostic, AST/module call |
| `parser_stmts.spl:2271` | `parse_while_expr` | diagnostic, AST/module call |
| `parser_stmts.spl:2286` | `parse_tuple_destructure_val` | diagnostic, AST/module call |
| `parser_stmts.spl:2341` | `parse_tuple_destructure_var` | diagnostic, AST/module call |
| `parser_stmts.spl:2386` | `parse_gpu_launch_stmt` | diagnostic, AST/module call |
| `string_interpolation_expand.spl:102` | `parse_interpolation_fragment` | none detected |
| `string_interpolation_expand.spl:172` | `parse_string_interpolation_parts` | none detected |
| `string_interpolation_expand.spl:178` | `parse_string_interpolation_regions` | none detected |

## Review required before program generation

For each candidate, trace its callees, token-kind and spelling predicates, control-flow progress, recovery, source span conversion, diagnostics, AST/module mutations, checkpoint commit/rollback, and post-parse transforms. The source-backed checkpoint inventory records the 18 direct `lex_snapshot_save` sites and lexer state that a program must preserve. This survey does not prove complete grammar/action coverage; the validator, scalar executor, independent differential corpus, and admission remain open.
