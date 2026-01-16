# Test Specification

*Generated: 2026-01-16 04:08:50*

## simple/std_lib/test/features/codegen

✅ **buffer_pool_spec.spl** (12ms)

✅ **cranelift_spec.spl** (68ms)

✅ **generator_codegen_spec.spl** (5ms)

✅ **llvm_backend_spec.spl** (4ms)

✅ **native_binary_spec.spl** (4ms)


## simple/std_lib/test/features/concurrency

✅ **actors_spec.spl** (23ms)

✅ **async_await_spec.spl** (104ms)

✅ **async_default_spec.spl** (22ms)

✅ **effect_inference_spec.spl** (3ms)

✅ **futures_spec.spl** (4ms)

✅ **generators_spec.spl** (3ms)

✅ **promise_type_spec.spl** (2ms)

✅ **suspension_operator_spec.spl** (2ms)


## simple/std_lib/test/features/control_flow

✅ **conditionals_spec.spl** (40ms)

✅ **enumerate_shorthand_spec.spl** (3ms)

✅ **error_handling_spec.spl** (28ms)

✅ **loops_spec.spl** (29ms)

✅ **match_spec.spl** (51ms)

✅ **with_statement_spec.spl** (2ms)


## simple/std_lib/test/features/data_structures

✅ **arrays_spec.spl** (45ms)

✅ **comprehensions_spec.spl** (4ms)

✅ **dicts_spec.spl** (34ms)

✅ **ranges_spec.spl** (6ms)

❌ **sets_spec.spl** (0ms)

```
Error: parse error: Unexpected token: expected identifier, found Union
```

❌ **strings_spec.spl** (0ms)

```
Error: parse error: Unexpected token: expected expression, found Ellipsis
```

✅ **tensor_dimensions_spec.spl** (3ms)

✅ **tuples_spec.spl** (42ms)


## simple/std_lib/test/features/infrastructure

✅ **ast_spec.spl** (4ms)

✅ **gc_spec.spl** (4ms)

❌ **hir_spec.spl** (0ms)

```
Error: parse error: Unexpected token: expected Fn, found Val
```

✅ **lexer_spec.spl** (2ms)

✅ **mir_spec.spl** (4ms)

✅ **package_manager_spec.spl** (5ms)

❌ **parser_spec.spl** (0ms)

```
Error: parse error: Unexpected token: expected expression, found FatArrow
```

✅ **runtime_value_spec.spl** (4ms)

✅ **smf_spec.spl** (4ms)


## simple/std_lib/test/features/language

✅ **channels_spec.spl** (3ms)

✅ **classes_spec.spl** (20ms)

✅ **closures_spec.spl** (5ms)

✅ **concurrency_spec.spl** (3ms)

✅ **functions_spec.spl** (52ms)

✅ **imports_spec.spl** (33ms)

✅ **lambda_spec.spl** (2ms)

✅ **macros_spec.spl** (3ms)

✅ **methods_spec.spl** (32ms)

✅ **naming_convention_mutability_spec.spl** (60ms)

✅ **static_polymorphism_spec.spl** (4ms)

✅ **structs_spec.spl** (29ms)

✅ **traits_spec.spl** (4ms)

✅ **variables_spec.spl** (38ms)


## simple/std_lib/test/features/ml

✅ **config_system_spec.spl** (46ms)

✅ **experiment_tracking_spec.spl** (2ms)

✅ **torch_caching_spec.spl** (67ms)

✅ **training_engine_spec.spl** (60ms)


## simple/std_lib/test/features/stdlib

❌ **each_method_spec.spl** (1ms)

```
Error: parse error: Unexpected token: expected Comma, found Assign
```

❌ **empty_predicate_spec.spl** (0ms)

```
Error: parse error: Unexpected token: expected expression, found DoubleColon
```

✅ **file_io_spec.spl** (38ms)

❌ **integer_iteration_spec.spl** (1ms)

```
Error: parse error: Unexpected token: expected identifier, found Underscore
```

✅ **json_spec.spl** (4ms)

❌ **number_trait_spec.spl** (2ms)

```
Error: compile failed: semantic: unsupported path call: ["i64", "zero"]
```

❌ **sorting_algorithms_spec.spl** (2ms)

```
Error: compile failed: semantic: unknown path: "SortAlgorithm"::InsertionSort
```

✅ **string_methods_spec.spl** (4ms)

✅ **symbol_table_spec.spl** (3ms)

✅ **try_operator_spec.spl** (3ms)


## simple/std_lib/test/features/syntax

❌ **brevity_syntax_spec.spl** (0ms)

```
Error: parse error: Unexpected token: expected Comma, found Integer(5)
```

❌ **custom_blocks_spec.spl** (1ms)

```
Error: parse error: Unexpected token: expected identifier, found FString([Literal("json")])
```


## simple/std_lib/test/features/testing_framework

✅ **after_each_spec.spl** (3ms)

✅ **before_each_spec.spl** (53ms)

✅ **context_blocks_spec.spl** (4ms)

✅ **describe_blocks_spec.spl** (3ms)

✅ **doctest_spec.spl** (3ms)

✅ **expect_matchers_spec.spl** (3ms)

✅ **it_examples_spec.spl** (3ms)


## simple/std_lib/test/features/types

✅ **basic_types_spec.spl** (32ms)

✅ **borrowing_spec.spl** (4ms)

✅ **enums_spec.spl** (32ms)

✅ **generics_spec.spl** (4ms)

✅ **memory_types_spec.spl** (3ms)

✅ **operators_spec.spl** (50ms)

✅ **option_result_spec.spl** (46ms)


## doc/features

❌ **feature_db.sdn** (0ms)

```
Error: feature db update failed: Invalid table row: expected 1 columns, found 0
```


---

## Summary

- **Total:** 81 tests
- **Passed:** 69 ✅
- **Failed:** 12 ❌
- **Duration:** 1387ms
