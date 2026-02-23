# Spec Documentation Catalog

Full mapping of all spec files to their generated documentation output.

**Total:** 296 spec files across 11 categories
**Has docstring:** 221 files
**Missing docstring:** 75 files (marked with ⚠)

Run `bin/simple sspec-docgen <spec_files...> --output <dir>` to generate docs.

---

## Language Features (`test/feature/usage/` → `doc/spec/feature/usage/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/usage/actor_model_spec.spl` | `usage/actor_model_spec.md` | ✅ |
| `test/feature/usage/actors_spec.spl` | `usage/actors_spec.md` | ✅ |
| `test/feature/usage/advanced_indexing_spec.spl` | `usage/advanced_indexing_spec.md` | ✅ |
| `test/feature/usage/alias_deprecated_spec.spl` | `usage/alias_deprecated_spec.md` | ✅ |
| `test/feature/usage/aop_architecture_rules_spec.spl` | `usage/aop_architecture_rules_spec.md` | ✅ |
| `test/feature/usage/aop_debug_log_spec.spl` | `usage/aop_debug_log_spec.md` | ⚠ |
| `test/feature/usage/aop_pointcut_spec.spl` | `usage/aop_pointcut_spec.md` | ✅ |
| `test/feature/usage/aop_spec.spl` | `usage/aop_spec.md` | ✅ |
| `test/feature/usage/arch_check_error_cases_spec.spl` | `usage/arch_check_error_cases_spec.md` | ⚠ |
| `test/feature/usage/architecture_spec.spl` | `usage/architecture_spec.md` | ⚠ |
| `test/feature/usage/arithmetic_spec.spl` | `usage/arithmetic_spec.md` | ✅ |
| `test/feature/usage/array_types_spec.spl` | `usage/array_types_spec.md` | ✅ |
| `test/feature/usage/assert_spec.spl` | `usage/assert_spec.md` | ✅ |
| `test/feature/usage/async_effects_spec.spl` | `usage/async_effects_spec.md` | ✅ |
| `test/feature/usage/async_features_spec.spl` | `usage/async_features_spec.md` | ✅ |
| `test/feature/usage/async_file_io_spec.spl` | `usage/async_file_io_spec.md` | ✅ |
| `test/feature/usage/basic_types_integer_literals_spec.spl` | `usage/basic_types_integer_literals_spec.md` | ✅ |
| `test/feature/usage/bitfield_spec.spl` | `usage/bitfield_spec.md` | ✅ |
| `test/feature/usage/borrowing_spec.spl` | `usage/borrowing_spec.md` | ✅ |
| `test/feature/usage/btree_basic_spec.spl` | `usage/btree_basic_spec.md` | ✅ |
| `test/feature/usage/call_site_label_spec.spl` | `usage/call_site_label_spec.md` | ✅ |
| `test/feature/usage/capability_system_spec.spl` | `usage/capability_system_spec.md` | ✅ |
| `test/feature/usage/capture_buffer_vreg_remapping_spec.spl` | `usage/capture_buffer_vreg_remapping_spec.md` | ✅ |
| `test/feature/usage/classes_spec.spl` | `usage/classes_spec.md` | ✅ |
| `test/feature/usage/class_invariant_spec.spl` | `usage/class_invariant_spec.md` | ✅ |
| `test/feature/usage/collections_spec.spl` | `usage/collections_spec.md` | ✅ |
| `test/feature/usage/collection_utilities_spec.spl` | `usage/collection_utilities_spec.md` | ✅ |
| `test/feature/usage/comments_spec.spl` | `usage/comments_spec.md` | ✅ |
| `test/feature/usage/component_spec.spl` | `usage/component_spec.md` | ✅ |
| `test/feature/usage/concurrency_primitives_spec.spl` | `usage/concurrency_primitives_spec.md` | ✅ |
| `test/feature/usage/context_blocks_spec.spl` | `usage/context_blocks_spec.md` | ✅ |
| `test/feature/usage/context_managers_spec.spl` | `usage/context_managers_spec.md` | ✅ |
| `test/feature/usage/contract_persistence_feature_spec.spl` | `usage/contract_persistence_feature_spec.md` | ⚠ |
| `test/feature/usage/contract_runtime_spec.spl` | `usage/contract_runtime_spec.md` | ✅ |
| `test/feature/usage/control_flow_if_else_spec.spl` | `usage/control_flow_if_else_spec.md` | ✅ |
| `test/feature/usage/cuda_spec.spl` | `usage/cuda_spec.md` | ⚠ |
| `test/feature/usage/custom_backend_spec.spl` | `usage/custom_backend_spec.md` | ⚠ |
| `test/feature/usage/custom_literal_spec.spl` | `usage/custom_literal_spec.md` | ⚠ |
| `test/feature/usage/decorators_spec.spl` | `usage/decorators_spec.md` | ✅ |
| `test/feature/usage/default_arguments_spec.spl` | `usage/default_arguments_spec.md` | ✅ |
| `test/feature/usage/dict_grammar_spec.spl` | `usage/dict_grammar_spec.md` | ✅ |
| `test/feature/usage/dictionary_types_spec.spl` | `usage/dictionary_types_spec.md` | ✅ |
| `test/feature/usage/di_error_cases_spec.spl` | `usage/di_error_cases_spec.md` | ⚠ |
| `test/feature/usage/di_extensions_feature_spec.spl` | `usage/di_extensions_feature_spec.md` | ⚠ |
| `test/feature/usage/di_injection_spec.spl` | `usage/di_injection_spec.md` | ✅ |
| `test/feature/usage/di_lock_all_phases_spec.spl` | `usage/di_lock_all_phases_spec.md` | ⚠ |
| `test/feature/usage/di_lock_feature_spec.spl` | `usage/di_lock_feature_spec.md` | ⚠ |
| `test/feature/usage/effect_annotations_spec.spl` | `usage/effect_annotations_spec.md` | ✅ |
| `test/feature/usage/effect_system_spec.spl` | `usage/effect_system_spec.md` | ✅ |
| `test/feature/usage/elif_val_pattern_binding_spec.spl` | `usage/elif_val_pattern_binding_spec.md` | ✅ |
| `test/feature/usage/enums_spec.spl` | `usage/enums_spec.md` | ✅ |
| `test/feature/usage/exists_check_spec.spl` | `usage/exists_check_spec.md` | ✅ |
| `test/feature/usage/experiment_tracking_spec.spl` | `usage/experiment_tracking_spec.md` | ✅ |
| `test/feature/usage/extern_functions_spec.spl` | `usage/extern_functions_spec.md` | ✅ |
| `test/feature/usage/feature_done_spec.spl` | `usage/feature_done_spec.md` | ✅ |
| `test/feature/usage/file_io_extended_spec.spl` | `usage/file_io_extended_spec.md` | ✅ |
| `test/feature/usage/file_watcher_spec.spl` | `usage/file_watcher_spec.md` | ✅ |
| `test/feature/usage/fixed_size_arrays_spec.spl` | `usage/fixed_size_arrays_spec.md` | ✅ |
| `test/feature/usage/fixed_size_edge_cases_spec.spl` | `usage/fixed_size_edge_cases_spec.md` | ✅ |
| `test/feature/usage/floor_division_fdiv_spec.spl` | `usage/floor_division_fdiv_spec.md` | ✅ |
| `test/feature/usage/format_string_with_spec.spl` | `usage/format_string_with_spec.md` | ✅ |
| `test/feature/usage/freeze_unfreeze_spec.spl` | `usage/freeze_unfreeze_spec.md` | ✅ |
| `test/feature/usage/function_alias_spec.spl` | `usage/function_alias_spec.md` | ⚠ |
| `test/feature/usage/functional_update_spec.spl` | `usage/functional_update_spec.md` | ✅ |
| `test/feature/usage/functions_spec.spl` | `usage/functions_spec.md` | ✅ |
| `test/feature/usage/future_body_execution_spec.spl` | `usage/future_body_execution_spec.md` | ✅ |
| `test/feature/usage/futures_promises_spec.spl` | `usage/futures_promises_spec.md` | ✅ |
| `test/feature/usage/gc_managed_default_spec.spl` | `usage/gc_managed_default_spec.md` | ✅ |
| `test/feature/usage/generator_state_machine_codegen_spec.spl` | `usage/generator_state_machine_codegen_spec.md` | ✅ |
| `test/feature/usage/generic_bytecode_spec.spl` | `usage/generic_bytecode_spec.md` | ⚠ |
| `test/feature/usage/generics_advanced_spec.spl` | `usage/generics_advanced_spec.md` | ✅ |
| `test/feature/usage/generics_spec.spl` | `usage/generics_spec.md` | ✅ |
| `test/feature/usage/gpu_basic_spec.spl` | `usage/gpu_basic_spec.md` | ⚠ |
| `test/feature/usage/gpu_kernels_spec.spl` | `usage/gpu_kernels_spec.md` | ✅ |
| `test/feature/usage/gpu_ptx_gen_spec.spl` | `usage/gpu_ptx_gen_spec.md` | ✅ |
| `test/feature/usage/guard_clause_spec.spl` | `usage/guard_clause_spec.md` | ✅ |
| `test/feature/usage/handle_pointers_spec.spl` | `usage/handle_pointers_spec.md` | ✅ |
| `test/feature/usage/hashmap_basic_spec.spl` | `usage/hashmap_basic_spec.md` | ✅ |
| `test/feature/usage/hashset_basic_spec.spl` | `usage/hashset_basic_spec.md` | ✅ |
| `test/feature/usage/hm_type_inference_spec.spl` | `usage/hm_type_inference_spec.md` | ⚠ |
| `test/feature/usage/impl_blocks_spec.spl` | `usage/impl_blocks_spec.md` | ✅ |
| `test/feature/usage/implicit_context_spec.spl` | `usage/implicit_context_spec.md` | ⚠ |
| `test/feature/usage/implicit_mul_spec.spl` | `usage/implicit_mul_spec.md` | ✅ |
| `test/feature/usage/indentation_blocks_spec.spl` | `usage/indentation_blocks_spec.md` | ✅ |
| `test/feature/usage/index_spec.spl` | `usage/index_spec.md` | ✅ |
| `test/feature/usage/interpreter_interface_spec.spl` | `usage/interpreter_interface_spec.md` | ✅ |
| `test/feature/usage/lambdas_closures_spec.spl` | `usage/lambdas_closures_spec.md` | ✅ |
| `test/feature/usage/line_continuation_spec.spl` | `usage/line_continuation_spec.md` | ✅ |
| `test/feature/usage/llvm_backend_aarch64_spec.spl` | `usage/llvm_backend_aarch64_spec.md` | ✅ |
| `test/feature/usage/llvm_backend_arm32_spec.spl` | `usage/llvm_backend_arm32_spec.md` | ✅ |
| `test/feature/usage/llvm_backend_i686_spec.spl` | `usage/llvm_backend_i686_spec.md` | ✅ |
| `test/feature/usage/llvm_backend_riscv32_spec.spl` | `usage/llvm_backend_riscv32_spec.md` | ✅ |
| `test/feature/usage/llvm_backend_riscv64_spec.spl` | `usage/llvm_backend_riscv64_spec.md` | ✅ |
| `test/feature/usage/llvm_backend_spec.spl` | `usage/llvm_backend_spec.md` | ✅ |
| `test/feature/usage/loops_spec.spl` | `usage/loops_spec.md` | ✅ |
| `test/feature/usage/macro_hygiene_spec.spl` | `usage/macro_hygiene_spec.md` | ✅ |
| `test/feature/usage/macros_spec.spl` | `usage/macros_spec.md` | ✅ |
| `test/feature/usage/macro_validation_spec.spl` | `usage/macro_validation_spec.md` | ✅ |
| `test/feature/usage/mat4_spec.spl` | `usage/mat4_spec.md` | ✅ |
| `test/feature/usage/math_blocks_spec.spl` | `usage/math_blocks_spec.md` | ✅ |
| `test/feature/usage/math_language_spec.spl` | `usage/math_language_spec.md` | ✅ |
| `test/feature/usage/matrix_multiplication_spec.spl` | `usage/matrix_multiplication_spec.md` | ✅ |
| `test/feature/usage/metaprogramming_spec.spl` | `usage/metaprogramming_spec.md` | ✅ |
| `test/feature/usage/method_alias_spec.spl` | `usage/method_alias_spec.md` | ✅ |
| `test/feature/usage/method_missing_spec.spl` | `usage/method_missing_spec.md` | ✅ |
| `test/feature/usage/minimal_spec.spl` | `usage/minimal_spec.md` | ⚠ |
| `test/feature/usage/module_loader_spec.spl` | `usage/module_loader_spec.md` | ✅ |
| `test/feature/usage/module_visibility_spec.spl` | `usage/module_visibility_spec.md` | ✅ |
| `test/feature/usage/multiline_syntax_spec.spl` | `usage/multiline_syntax_spec.md` | ✅ |
| `test/feature/usage/multiple_assignment_spec.spl` | `usage/multiple_assignment_spec.md` | ✅ |
| `test/feature/usage/mutability_control_spec.spl` | `usage/mutability_control_spec.md` | ✅ |
| `test/feature/usage/mutable_by_default_spec.spl` | `usage/mutable_by_default_spec.md` | ✅ |
| `test/feature/usage/named_arg_equals_spec.spl` | `usage/named_arg_equals_spec.md` | ✅ |
| `test/feature/usage/named_arguments_spec.spl` | `usage/named_arguments_spec.md` | ✅ |
| `test/feature/usage/networking_spec.spl` | `usage/networking_spec.md` | ✅ |
| `test/feature/usage/no_paren_calls_spec.spl` | `usage/no_paren_calls_spec.md` | ✅ |
| `test/feature/usage/note_sdn_feature_spec.spl` | `usage/note_sdn_feature_spec.md` | ⚠ |
| `test/feature/usage/null_coalescing_try_operator_spec.spl` | `usage/null_coalescing_try_operator_spec.md` | ✅ |
| `test/feature/usage/numeric_literals_spec.spl` | `usage/numeric_literals_spec.md` | ✅ |
| `test/feature/usage/operators_advanced_spec.spl` | `usage/operators_advanced_spec.md` | ✅ |
| `test/feature/usage/operators_arithmetic_spec.spl` | `usage/operators_arithmetic_spec.md` | ✅ |
| `test/feature/usage/optional_chaining_spec.spl` | `usage/optional_chaining_spec.md` | ✅ |
| `test/feature/usage/option_type_spec.spl` | `usage/option_type_spec.md` | ✅ |
| `test/feature/usage/parser_contextual_keywords_simple_spec.spl` | `usage/parser_contextual_keywords_simple_spec.md` | ✅ |
| `test/feature/usage/parser_control_flow_spec.spl` | `usage/parser_control_flow_spec.md` | ✅ |
| `test/feature/usage/parser_declarations_spec.spl` | `usage/parser_declarations_spec.md` | ✅ |
| `test/feature/usage/parser_default_keyword_spec.spl` | `usage/parser_default_keyword_spec.md` | ⚠ |
| `test/feature/usage/parser_deprecation_warnings_spec.spl` | `usage/parser_deprecation_warnings_spec.md` | ✅ |
| `test/feature/usage/parser_dual_argument_syntax_spec.spl` | `usage/parser_dual_argument_syntax_spec.md` | ✅ |
| `test/feature/usage/parser_edge_cases_spec.spl` | `usage/parser_edge_cases_spec.md` | ✅ |
| `test/feature/usage/parser_error_recovery_spec.spl` | `usage/parser_error_recovery_spec.md` | ✅ |
| `test/feature/usage/parser_expressions_spec.spl` | `usage/parser_expressions_spec.md` | ✅ |
| `test/feature/usage/parser_functions_spec.spl` | `usage/parser_functions_spec.md` | ✅ |
| `test/feature/usage/parser_keywords_spec.spl` | `usage/parser_keywords_spec.md` | ✅ |
| `test/feature/usage/parser_literals_spec.spl` | `usage/parser_literals_spec.md` | ✅ |
| `test/feature/usage/parser_operators_spec.spl` | `usage/parser_operators_spec.md` | ✅ |
| `test/feature/usage/parser_skip_basic_spec.spl` | `usage/parser_skip_basic_spec.md` | ⚠ |
| `test/feature/usage/parser_skip_keyword_spec.spl` | `usage/parser_skip_keyword_spec.md` | ⚠ |
| `test/feature/usage/parser_static_keyword_spec.spl` | `usage/parser_static_keyword_spec.md` | ⚠ |
| `test/feature/usage/parser_syntax_validation_spec.spl` | `usage/parser_syntax_validation_spec.md` | ✅ |
| `test/feature/usage/parser_type_annotations_spec.spl` | `usage/parser_type_annotations_spec.md` | ✅ |
| `test/feature/usage/pass_unit_equivalence_spec.spl` | `usage/pass_unit_equivalence_spec.md` | ✅ |
| `test/feature/usage/pass_variants_spec.spl` | `usage/pass_variants_spec.md` | ⚠ |
| `test/feature/usage/pattern_matching_advanced_spec.spl` | `usage/pattern_matching_advanced_spec.md` | ✅ |
| `test/feature/usage/pattern_matching_spec.spl` | `usage/pattern_matching_spec.md` | ✅ |
| `test/feature/usage/pipeline_components_spec.spl` | `usage/pipeline_components_spec.md` | ✅ |
| `test/feature/usage/placeholder_lambda_spec.spl` | `usage/placeholder_lambda_spec.md` | ✅ |
| `test/feature/usage/primitive_types_spec.spl` | `usage/primitive_types_spec.md` | ✅ |
| `test/feature/usage/quat_spec.spl` | `usage/quat_spec.md` | ✅ |
| `test/feature/usage/range_step_by_spec.spl` | `usage/range_step_by_spec.md` | ✅ |
| `test/feature/usage/resource_cleanup_spec.spl` | `usage/resource_cleanup_spec.md` | ⚠ |
| `test/feature/usage/result_type_spec.spl` | `usage/result_type_spec.md` | ✅ |
| `test/feature/usage/rust_simple_ffi_spec.spl` | `usage/rust_simple_ffi_spec.md` | ✅ |
| `test/feature/usage/safe_unwrap_operators_spec.spl` | `usage/safe_unwrap_operators_spec.md` | ✅ |
| `test/feature/usage/sandboxing_spec.spl` | `usage/sandboxing_spec.md` | ✅ |
| `test/feature/usage/scene_node_spec.spl` | `usage/scene_node_spec.md` | ✅ |
| `test/feature/usage/serial_driver_spec.spl` | `usage/serial_driver_spec.md` | ✅ |
| `test/feature/usage/set_literal_spec.spl` | `usage/set_literal_spec.md` | ⚠ |
| `test/feature/usage/shared_pointers_spec.spl` | `usage/shared_pointers_spec.md` | ✅ |
| `test/feature/usage/single_line_functions_spec.spl` | `usage/single_line_functions_spec.md` | ✅ |
| `test/feature/usage/stackless_coroutines_spec.spl` | `usage/stackless_coroutines_spec.md` | ✅ |
| `test/feature/usage/static_const_declarations_spec.spl` | `usage/static_const_declarations_spec.md` | ✅ |
| `test/feature/usage/static_method_resolution_spec.spl` | `usage/static_method_resolution_spec.md` | ⚠ |
| `test/feature/usage/string_interpolation_spec.spl` | `usage/string_interpolation_spec.md` | ✅ |
| `test/feature/usage/struct_shorthand_spec.spl` | `usage/struct_shorthand_spec.md` | ✅ |
| `test/feature/usage/structs_spec.spl` | `usage/structs_spec.md` | ✅ |
| `test/feature/usage/symbols_atoms_spec.spl` | `usage/symbols_atoms_spec.md` | ✅ |
| `test/feature/usage/syntax_spec.spl` | `usage/syntax_spec.md` | ✅ |
| `test/feature/usage/table_spec.spl` | `usage/table_spec.md` | ✅ |
| `test/feature/usage/target_arch_spec.spl` | `usage/target_arch_spec.md` | ✅ |
| `test/feature/usage/target_defaults_spec.spl` | `usage/target_defaults_spec.md` | ✅ |
| `test/feature/usage/tensor_bridge_spec.spl` | `usage/tensor_bridge_spec.md` | ⚠ |
| `test/feature/usage/tensor_interface_spec.spl` | `usage/tensor_interface_spec.md` | ✅ |
| `test/feature/usage/tensor_spec.spl` | `usage/tensor_spec.md` | ✅ |
| `test/feature/usage/trailing_blocks_spec.spl` | `usage/trailing_blocks_spec.md` | ✅ |
| `test/feature/usage/trait_coherence_spec.spl` | `usage/trait_coherence_spec.md` | ✅ |
| `test/feature/usage/trait_forwarding_spec.spl` | `usage/trait_forwarding_spec.md` | ⚠ |
| `test/feature/usage/trait_keyword_all_phases_spec.spl` | `usage/trait_keyword_all_phases_spec.md` | ⚠ |
| `test/feature/usage/traits_spec.spl` | `usage/traits_spec.md` | ✅ |
| `test/feature/usage/transform_spec.spl` | `usage/transform_spec.md` | ✅ |
| `test/feature/usage/treesitter_cursor_spec.spl` | `usage/treesitter_cursor_spec.md` | ✅ |
| `test/feature/usage/treesitter_error_recovery_spec.spl` | `usage/treesitter_error_recovery_spec.md` | ✅ |
| `test/feature/usage/treesitter_lexer_spec.spl` | `usage/treesitter_lexer_spec.md` | ✅ |
| `test/feature/usage/treesitter_parser_spec.spl` | `usage/treesitter_parser_spec.md` | ✅ |
| `test/feature/usage/treesitter_query_spec.spl` | `usage/treesitter_query_spec.md` | ✅ |
| `test/feature/usage/treesitter_tree_spec.spl` | `usage/treesitter_tree_spec.md` | ✅ |
| `test/feature/usage/tuple_types_spec.spl` | `usage/tuple_types_spec.md` | ✅ |
| `test/feature/usage/type_aliases_spec.spl` | `usage/type_aliases_spec.md` | ✅ |
| `test/feature/usage/type_conversion_spec.spl` | `usage/type_conversion_spec.md` | ✅ |
| `test/feature/usage/type_inference_spec.spl` | `usage/type_inference_spec.md` | ✅ |
| `test/feature/usage/types_spec.spl` | `usage/types_spec.md` | ✅ |
| `test/feature/usage/ufcs_spec.spl` | `usage/ufcs_spec.md` | ✅ |
| `test/feature/usage/underscore_wildcard_spec.spl` | `usage/underscore_wildcard_spec.md` | ✅ |
| `test/feature/usage/union_types_spec.spl` | `usage/union_types_spec.md` | ✅ |
| `test/feature/usage/unique_pointers_spec.spl` | `usage/unique_pointers_spec.md` | ✅ |
| `test/feature/usage/unit_types_spec.spl` | `usage/unit_types_spec.md` | ✅ |
| `test/feature/usage/unnamed_duplicate_typed_args_spec.spl` | `usage/unnamed_duplicate_typed_args_spec.md` | ✅ |
| `test/feature/usage/variables_let_bindings_spec.spl` | `usage/variables_let_bindings_spec.md` | ✅ |
| `test/feature/usage/vec3_spec.spl` | `usage/vec3_spec.md` | ✅ |
| `test/feature/usage/vhdl_golden_spec.spl` | `usage/vhdl_golden_spec.md` | ⚠ |
| `test/feature/usage/vhdl_spec.spl` | `usage/vhdl_spec.md` | ⚠ |
| `test/feature/usage/visibility_modifiers_spec.spl` | `usage/visibility_modifiers_spec.md` | ✅ |
| `test/feature/usage/vulkan_spec.spl` | `usage/vulkan_spec.md` | ⚠ |
| `test/feature/usage/walrus_operator_spec.spl` | `usage/walrus_operator_spec.md` | ⚠ |
| `test/feature/usage/wasm_compile_spec.spl` | `usage/wasm_compile_spec.md` | ⚠ |
| `test/feature/usage/weak_pointers_spec.spl` | `usage/weak_pointers_spec.md` | ✅ |
| `test/feature/usage/web_framework_spec.spl` | `usage/web_framework_spec.md` | ✅ |
| `test/feature/usage/x86_boot_spec.spl` | `usage/x86_boot_spec.md` | ✅ |

---

## Application (`test/feature/app/` → `doc/spec/feature/app/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/app/backend_port_feature_spec.spl` | `app/backend_port_feature_spec.md` | ⚠ |
| `test/feature/app/bootstrap_spec.spl` | `app/bootstrap_spec.md` | ⚠ |
| `test/feature/app/codegen_parity_completion_spec.spl` | `app/codegen_parity_completion_spec.md` | ✅ |
| `test/feature/app/code_quality_tools_spec.spl` | `app/code_quality_tools_spec.md` | ✅ |
| `test/feature/app/compiler_services_error_cases_spec.spl` | `app/compiler_services_error_cases_spec.md` | ⚠ |
| `test/feature/app/compiler_services_feature_spec.spl` | `app/compiler_services_feature_spec.md` | ⚠ |
| `test/feature/app/config_env_spec.spl` | `app/config_env_spec.md` | ✅ |
| `test/feature/app/config_loader_spec.spl` | `app/config_loader_spec.md` | ✅ |
| `test/feature/app/database_resource_spec.spl` | `app/database_resource_spec.md` | ✅ |
| `test/feature/app/database_sync_spec.spl` | `app/database_sync_spec.md` | ⚠ |
| `test/feature/app/easy_fix_rules_spec.spl` | `app/easy_fix_rules_spec.md` | ✅ |
| `test/feature/app/easy_fix_spec.spl` | `app/easy_fix_spec.md` | ✅ |
| `test/feature/app/fault_detection_spec.spl` | `app/fault_detection_spec.md` | ✅ |
| `test/feature/app/install_spec.spl` | `app/install_spec.md` | ✅ |
| `test/feature/app/linker_gen_spec.spl` | `app/linker_gen_spec.md` | ✅ |
| `test/feature/app/mcp_debug_log_spec.spl` | `app/mcp_debug_log_spec.md` | ⚠ |
| `test/feature/app/mcp_diag_spec.spl` | `app/mcp_diag_spec.md` | ⚠ |
| `test/feature/app/mcp_log_store_spec.spl` | `app/mcp_log_store_spec.md` | ⚠ |
| `test/feature/app/mcp/server_spec.spl` | `app/server_spec.md` | ✅ |
| `test/feature/app/native_exe_spec.spl` | `app/native_exe_spec.md` | ✅ |
| `test/feature/app/publish_spec.spl` | `app/publish_spec.md` | ✅ |
| `test/feature/app/sdoctest_spec.spl` | `app/sdoctest_spec.md` | ✅ |
| `test/feature/app/search_spec.spl` | `app/search_spec.md` | ✅ |
| `test/feature/app/shell_api_spec.spl` | `app/shell_api_spec.md` | ✅ |

---

## Compiler (`test/feature/compiler/` → `doc/spec/feature/compiler/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/compiler/backend/differential_llvm_spec.spl` | `compiler/differential_llvm_spec.md` | ⚠ |
| `test/feature/compiler/backend/native/got_plt_spec.spl` | `compiler/got_plt_spec.md` | ⚠ |
| `test/feature/compiler/bootstrap_spec.spl` | `compiler/bootstrap_spec.md` | ⚠ |
| `test/feature/compiler/bootstrap_system_spec.spl` | `compiler/bootstrap_system_spec.md` | ⚠ |
| `test/feature/compiler/compiler_basics_spec.spl` | `compiler/compiler_basics_spec.md` | ✅ |
| `test/feature/compiler/driver_native_spec.spl` | `compiler/driver_native_spec.md` | ✅ |
| `test/feature/compiler/linker/direct_elf_basic_spec.spl` | `compiler/direct_elf_basic_spec.md` | ⚠ |
| `test/feature/compiler/linker/direct_elf_spec.spl` | `compiler/direct_elf_spec.md` | ⚠ |
| `test/feature/compiler/mir_builder_spec.spl` | `compiler/mir_builder_spec.md` | ✅ |
| `test/feature/compiler/mir_complex_spec.spl` | `compiler/mir_complex_spec.md` | ✅ |
| `test/feature/compiler/mir_native_spec.spl` | `compiler/mir_native_spec.md` | ✅ |
| `test/feature/compiler/native_compile_elf_spec.spl` | `compiler/native_compile_elf_spec.md` | ✅ |
| `test/feature/compiler/pipeline_multi_spec.spl` | `compiler/pipeline_multi_spec.md` | ✅ |
| `test/feature/compiler/pipeline_native_spec.spl` | `compiler/pipeline_native_spec.md` | ✅ |
| `test/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl` | `compiler/basic_expressions_spec.md` | ✅ |
| `test/feature/compiler/sample/python_inspired_sample/classes_spec.spl` | `compiler/classes_spec.md` | ✅ |
| `test/feature/compiler/sample/python_inspired_sample/collections_spec.spl` | `compiler/collections_spec.md` | ✅ |
| `test/feature/compiler/sample/python_inspired_sample/control_flow_spec.spl` | `compiler/control_flow_spec.md` | ✅ |
| `test/feature/compiler/sample/python_inspired_sample/functions_spec.spl` | `compiler/functions_spec.md` | ✅ |
| `test/feature/compiler/type_inference_string_slice_spec.spl` | `compiler/type_inference_string_slice_spec.md` | ✅ |

---

## Developer Tools / DAP (`test/feature/dap/` → `doc/spec/feature/dap/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/dap/breakpoint_management_spec.spl` | `dap/breakpoint_management_spec.md` | ✅ |
| `test/feature/dap/dap_spec.spl` | `dap/dap_spec.md` | ⚠ |
| `test/feature/dap/debug_state_spec.spl` | `dap/debug_state_spec.md` | ✅ |
| `test/feature/dap/integration_spec.spl` | `dap/integration_spec.md` | ✅ |
| `test/feature/dap/stack_trace_spec.spl` | `dap/stack_trace_spec.md` | ✅ |
| `test/feature/dap/step_modes_spec.spl` | `dap/step_modes_spec.md` | ✅ |

---

## Runtime / Interpreter (`test/feature/interpreter/` → `doc/spec/feature/interpreter/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/interpreter/control_flow_spec.spl` | `interpreter/control_flow_spec.md` | ⚠ |
| `test/feature/interpreter/interpreter_basics_spec.spl` | `interpreter/interpreter_basics_spec.md` | ✅ |
| `test/feature/interpreter/interpreter_sample_spec.spl` | `interpreter/interpreter_sample_spec.md` | ✅ |
| `test/feature/interpreter/runtime_error_stack_spec.spl` | `interpreter/runtime_error_stack_spec.md` | ⚠ |
| `test/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl` | `interpreter/basic_expressions_spec.md` | ✅ |
| `test/feature/interpreter/sample/python_inspired_sample/collections_spec.spl` | `interpreter/collections_spec.md` | ✅ |
| `test/feature/interpreter/sample/python_inspired_sample/control_flow_spec.spl` | `interpreter/control_flow_spec.md` | ✅ |
| `test/feature/interpreter/sample/python_inspired_sample/functions_mixed_spec.spl` | `interpreter/functions_mixed_spec.md` | ✅ |
| `test/feature/interpreter/sample/python_inspired_sample/functions_print_spec.spl` | `interpreter/functions_print_spec.md` | ✅ |
| `test/feature/interpreter/sample/python_inspired_sample/functions_return_spec.spl` | `interpreter/functions_return_spec.md` | ✅ |
| `test/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.spl` | `interpreter/none_nil_handling_spec.md` | ✅ |
| `test/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl` | `interpreter/variables_assignment_spec.md` | ✅ |

---

## Baremetal (`test/feature/baremetal/` → `doc/spec/feature/baremetal/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/baremetal/allocator_spec.spl` | `baremetal/allocator_spec.md` | ⚠ |
| `test/feature/baremetal/arm32_boot_spec.spl` | `baremetal/arm32_boot_spec.md` | ⚠ |
| `test/feature/baremetal/arm64_boot_spec.spl` | `baremetal/arm64_boot_spec.md` | ⚠ |
| `test/feature/baremetal/boot_test_spec.spl` | `baremetal/boot_test_spec.md` | ⚠ |
| `test/feature/baremetal/debug_boot_spec.spl` | `baremetal/debug_boot_spec.md` | ⚠ |
| `test/feature/baremetal/hello_riscv32_semihost_spec.spl` | `baremetal/hello_riscv32_semihost_spec.md` | ⚠ |
| `test/feature/baremetal/inline_asm_integration_spec.spl` | `baremetal/inline_asm_integration_spec.md` | ⚠ |
| `test/feature/baremetal/interrupt_spec.spl` | `baremetal/interrupt_spec.md` | ⚠ |
| `test/feature/baremetal/riscv64_boot_spec.spl` | `baremetal/riscv64_boot_spec.md` | ⚠ |
| `test/feature/baremetal/startup_spec.spl` | `baremetal/startup_spec.md` | ⚠ |
| `test/feature/baremetal/syscall_spec.spl` | `baremetal/syscall_spec.md` | ⚠ |
| `test/feature/baremetal/x86_64_boot_spec.spl` | `baremetal/x86_64_boot_spec.md` | ⚠ |
| `test/feature/baremetal/x86_boot_spec.spl` | `baremetal/x86_boot_spec.md` | ⚠ |

---

## Standard Library (`test/feature/lib/` → `doc/spec/feature/lib/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/lib/import_debug_spec.spl` | `lib/import_debug_spec.md` | ⚠ |
| `test/feature/lib/mcp/core_spec.spl` | `lib/core_spec.md` | ⚠ |
| `test/feature/lib/mcp/handler_registry_spec.spl` | `lib/handler_registry_spec.md` | ⚠ |
| `test/feature/lib/mcp/helpers_spec.spl` | `lib/helpers_spec.md` | ⚠ |
| `test/feature/lib/mcp/integration_spec.spl` | `lib/integration_spec.md` | ⚠ |
| `test/feature/lib/mcp/schema_spec.spl` | `lib/schema_spec.md` | ⚠ |
| `test/feature/lib/minimal_spec.spl` | `lib/minimal_spec.md` | ⚠ |
| `test/feature/lib/std/helpers_example_spec.spl` | `lib/helpers_example_spec.md` | ⚠ |

---

## I/O (`test/feature/io/` → `doc/spec/feature/io/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/io/native_ops_spec.spl` | `io/native_ops_spec.md` | ⚠ |

---

## Platform (`test/feature/platform/` → `doc/spec/feature/platform/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/platform/cross_platform_spec.spl` | `platform/cross_platform_spec.md` | ⚠ |
| `test/feature/platform/windows_spec.spl` | `platform/windows_spec.md` | ⚠ |

---

## Tooling / Watcher (`test/feature/watcher/` → `doc/spec/feature/watcher/`)

| Spec File | Doc Output | Has Docstring |
|-----------|------------|---------------|
| `test/feature/watcher/watcher_app_spec.spl` | `watcher/watcher_app_spec.md` | ✅ |
| `test/feature/watcher/watcher_basics_spec.spl` | `watcher/watcher_basics_spec.md` | ✅ |

---

## FFI (`test/feature/ffi/` — non-standard naming)

| File | Notes |
|------|-------|
| `test/feature/ffi/ffi_hello_world.spl` | FFI hello world (not `_spec.spl`) |
| `test/feature/ffi/syscalls_manual_verify.spl` | Manual syscall verification |
| `test/feature/ffi/syscalls_test.spl` | Syscall tests (not `_spec.spl`) |

---

_To generate all docs, run:_
```bash
bin/simple sspec-docgen $(find test/feature -name '*_spec.spl') --output doc/spec/feature
```
