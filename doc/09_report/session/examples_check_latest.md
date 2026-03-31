# Examples Check

- Root: `examples/02_language_features`
- Mode: `compile`
- Binary: `bin/simple`
- Timeout: `10s`
- Files discovered: `11`



## examples/02_language_features/bdd_spec/advanced_features_example.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
[33mwarning[0m: Deprecated: 'import' keyword
  --> /home/ormastes/dev/pub/simple/examples/02_language_features/bdd_spec/advanced_features_example.spl:4:1
   |
  4 | import spec.{describe, context, it, expect, before_each, after_each, let_lazy, shared_examples, it_behaves_like, context_def, slow_it}
   | ^

Use 'use' instead of 'import'

Example: use std.spec.* instead of import std.spec

[33mwarning[0m: Deprecated: 'import' keyword
  --> /home/ormastes/dev/pub/simple/examples/02_language_features/bdd_spec/advanced_features_example.spl:5:1
```

### Stdout

```text
2026-03-31T04:12:15.924675Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=SkipCondition
2026-03-31T04:12:15.924801Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=create_skip_condition
2026-03-31T04:12:15.924824Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_platforms
2026-03-31T04:12:15.924845Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_runtimes
2026-03-31T04:12:15.924864Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_profiles
2026-03-31T04:12:15.924883Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_architectures
2026-03-31T04:12:15.924902Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_features
2026-03-31T04:12:15.924930Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_version
2026-03-31T04:12:15.924952Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_hardware
2026-03-31T04:12:15.924972Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_requires
2026-03-31T04:12:15.924991Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_env_vars
2026-03-31T04:12:15.925010Z  WARN ThreadId(02) compile_file_to_smf_with_options{out="/tmp/simple-example-check.smf" options=CompileOptions { parallel_threads: None, parallel: false, profile: false, read_strategy: Auto, verbose: false, coverage: false, coverage_output: None, emit_ast: None, emit_hir: None, emit_mir: None, deterministic: false, build_timestamp: None, log_path: None, allow_deprecated: false, memory_limit: 1073741824, memory_limit_fail: true }}:compile:load_and_merge_module{path=["spec"]}: simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers: 619: Export statement references undefined symbol name=matches_fs_features
```


## examples/02_language_features/bdd_spec/calculator_example.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
error: compile failed (examples/02_language_features/bdd_spec/calculator_example.spl): parse: in "/home/ormastes/dev/pub/simple/examples/02_language_features/bdd_spec/calculator_example.spl": Unexpected token: expected expression, found Colon
```


## Summary

- Total: `3`
- Passed: `1`
- Failed: `2`
- Crashed: `0`
- Timed out: `0`

