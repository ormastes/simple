# Examples Check

- Root: `examples`
- Mode: `compile`
- Binary: `bin/simple`
- Timeout: `15s`
- Files discovered: `993`


## examples/01_getting_started/hello_standalone/main.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /mnt/data/worktrees/simple-main/src/lib/string_core.spl:3:1
   |
  3 | export use lib.common.string_core.*
   | ^

Use explicit exports instead

Example: export use module.{A, B, C} or export A, B from module
```

## examples/01_getting_started/hello_taskbar/app.manifest.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /mnt/data/worktrees/simple-main/src/lib/nogc_sync_mut/binary_io.spl:3:1
   |
  3 | export use std.common.binary_io.*
   | ^

Use explicit exports instead

Example: export use module.{A, B, C} or export A, B from module
```

## examples/01_getting_started/hello_taskbar/app_manifest.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /mnt/data/worktrees/simple-main/src/lib/nogc_sync_mut/binary_io.spl:3:1
   |
  3 | export use std.common.binary_io.*
   | ^

Use explicit exports instead

Example: export use module.{A, B, C} or export A, B from module
```

## examples/01_getting_started/hello_taskbar/main.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /mnt/data/worktrees/simple-main/src/lib/nogc_sync_mut/binary_io.spl:3:1
   |
  3 | export use std.common.binary_io.*
   | ^

Use explicit exports instead

Example: export use module.{A, B, C} or export A, B from module
```

## examples/02_language_features/bdd_spec/advanced_features_example.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Deprecated: 'import' keyword
  --> /mnt/data/worktrees/simple-main/examples/02_language_features/bdd_spec/advanced_features_example.spl:4:1
   |
  4 | import spec.{describe, context, it, expect, before_each, after_each, let_lazy, shared_examples, it_behaves_like, context_def, slow_it}
   | ^

Use 'use' instead of 'import'

Example: use std.spec.* instead of import std.spec
```

## examples/02_language_features/bdd_spec/calculator_example.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Deprecated: 'import' keyword
  --> /mnt/data/worktrees/simple-main/examples/02_language_features/bdd_spec/calculator_example.spl:4:1
   |
  4 | import spec.{describe, context, it, expect, before_each, after_each}
   | ^

Use 'use' instead of 'import'

Example: use std.spec.* instead of import std.spec
```

## examples/02_language_features/blocks/custom_blocks.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/blocks/custom_blocks.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/blocks/custom_blocks.spl": function arguments: expected Comma, found RBrace
```

## examples/02_language_features/blocks/user_defined_blocks.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /mnt/data/worktrees/simple-main/src/compiler/15.blocks/blocks/modes.spl:6:1
   |
  6 | export use compiler.frontend.block_types.*
   | ^

Use explicit exports instead

Example: export use module.{A, B, C} or export A, B from module
```

## examples/02_language_features/execution_context.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/execution_context.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/execution_context.spl": Syntax error at 28:12: reserved keyword 'val' cannot be used as a parameter name
```

## examples/02_language_features/lean_verification/admitted_debt.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/lean_verification/admitted_debt.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/lean_verification/admitted_debt.spl": Unexpected token: expected Newline, found Identifier { name: "data", pattern: Immutable }
```

## examples/02_language_features/lean_verification/basic_theorem.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/lean_verification/basic_theorem.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/lean_verification/basic_theorem.spl": Unexpected token: expected Newline, found Bool(true)
```

## examples/02_language_features/lean_verification/contract_verify.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/lean_verification/contract_verify.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/lean_verification/contract_verify.spl": Unexpected token: expected Newline, found Identifier { name: "b", pattern: Immutable }
```

## examples/02_language_features/lean_verification/external_proof.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/lean_verification/external_proof.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/lean_verification/external_proof.spl": Unexpected token: expected Newline, found Identifier { name: "n", pattern: Immutable }
```

## examples/02_language_features/lean_verification/failed_proof.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/lean_verification/failed_proof.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/lean_verification/failed_proof.spl": Unexpected token: expected Newline, found Identifier { name: "ret", pattern: Immutable }
```

## examples/02_language_features/lean_verification/ghost_spec.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/lean_verification/ghost_spec.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/lean_verification/ghost_spec.spl": Unexpected token: expected Newline, found Identifier { name: "is_sorted", pattern: Immutable }
```

## examples/02_language_features/lean_verification/lean_block.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/lean_verification/lean_block.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/lean_verification/lean_block.spl": Unexpected token: expected Newline, found Identifier { name: "ret", pattern: Immutable }
```

## examples/02_language_features/polymorphism/static_polymorphism.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/polymorphism/static_polymorphism.spl): codegen: Failed to parse object into relocation-aware SMF: Invalid data: Failed to parse object file: Invalid section: relocation source section .data.rel.ro.subsection is not executable code
```

## examples/02_language_features/syntax/async_syntax.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/syntax/async_syntax.spl): semantic: examples/02_language_features/syntax/async_syntax.spl: cannot compile to standalone SMF: 3 function(s) contain constructs that require the interpreter:
  - fetch_data: [AsyncAwait]
  - fetch_with_retry: [AsyncAwait]
  - main: [AsyncAwait]
```

## examples/02_language_features/syntax/attribute_syntax.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/syntax/attribute_syntax.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/syntax/attribute_syntax.spl": Unexpected token: expected Fn, found Identifier { name: "it", pattern: Immutable }
```

## examples/02_language_features/syntax/spawn_syntax.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/02_language_features/syntax/spawn_syntax.spl): parse: in "/mnt/data/worktrees/simple-main/examples/02_language_features/syntax/spawn_syntax.spl": Unexpected token: expected identifier, found Dot
```

## examples/03_concurrency/actor_basics.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/03_concurrency/actor_basics.spl): semantic: examples/03_concurrency/actor_basics.spl: cannot compile to standalone SMF: 3 function(s) contain constructs that require the interpreter:
  - example_ask_reply: [TryOperator]
  - get_actor_runtime: [PatternMatch]
  - log_dispatch_text: [TryOperator]
```

## examples/03_concurrency/async_basics.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
warning: public function `process_run_with_limits` has 2 co-compiled definitions with 2 differing signatures ((text,[text],i64,i64)->Tuple([text, text, i32]) vs (text,[text],i64,i64,i64,i64,i64)->ProcessResult); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
warning: public function `process_wait` has 2 co-compiled definitions with 2 differing signatures ((i64)->i64 vs (i64,i64)->i64); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
warning: public function `shell` has 3 co-compiled definitions with 3 differing signatures ((text)->ProcessResult vs (text)->ShellResult vs (text)->i64); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
error: compile failed (examples/03_concurrency/async_basics.spl): semantic: examples/03_concurrency/async_basics.spl: Undefined("undefined identifier: panic")
```

## examples/03_concurrency/async_basics_alt.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
warning: public function `shell` has 2 co-compiled definitions with 2 differing signatures ((text)->ProcessResult vs (text)->ShellResult); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
warning: public function `spawn` has 2 co-compiled definitions with 2 differing signatures ((Function { params: [], ret: Some(Generic { name: "Future", args: [T] }) })->Task vs (Generic { name: "Future", args: [T] })->i64); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
error: compile failed (examples/03_concurrency/async_basics_alt.spl): semantic: examples/03_concurrency/async_basics_alt.spl: Undefined("undefined identifier: panic")
```

## examples/03_concurrency/async_structure.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
warning: public function `shell` has 2 co-compiled definitions with 2 differing signatures ((text)->ProcessResult vs (text)->ShellResult); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
error: compile failed (examples/03_concurrency/async_structure.spl): semantic: examples/03_concurrency/async_structure.spl: Undefined("undefined identifier: panic")
```

## examples/03_concurrency/concurrency_modes.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/03_concurrency/concurrency_modes.spl): parse: in "/mnt/data/worktrees/simple-main/examples/03_concurrency/concurrency_modes.spl": Unexpected token: expected Fn, found Mod
```

## examples/04_data_formats/sdn_parser.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
warning: public function `shell` has 2 co-compiled definitions with 2 differing signatures ((text)->ProcessResult vs (text)->ShellResult); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
error: compile failed (examples/04_data_formats/sdn_parser.spl): semantic: examples/04_data_formats/sdn_parser.spl: cannot compile to standalone SMF: 13 function(s) contain constructs that require the interpreter:
  - cli_arg_at: [TryOperator]
  - cli_arg_count: [TryOperator]
  - env_get_or: [TryOperator]
  - example_basic_parsing: [TryOperator]
  - example_structured_extraction: [TryOperator]
  - example_table_format: [TryOperator]
  - file_read: [TryOperator]
  - file_read_bytes: [TryOperator]
```

## examples/05_stdlib/platform_library.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: '#[runtime_intrinsics]' uses deprecated syntax, use '@runtime_intrinsics' instead
  --> /mnt/data/worktrees/simple-main/src/app/io/process_env_ops.spl:1:1
   |
  1 | #[runtime_intrinsics]
   | ^

Replace '#[runtime_intrinsics]' with '@runtime_intrinsics'

[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /mnt/data/worktrees/simple-main/src/lib/string_core.spl:3:1
```

## examples/05_stdlib/spipe/.claude/templates/spipe_template.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/05_stdlib/spipe/.claude/templates/spipe_template.spl): parse: in "/mnt/data/worktrees/simple-main/examples/05_stdlib/spipe/.claude/templates/spipe_template.spl": Unexpected token: expected Fn, found Assign
```

## examples/06_io/file/file_staging.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Deprecated syntax for static method/variant access
  --> /mnt/data/worktrees/simple-main/examples/06_io/file/file_staging.spl:27:26
   |
 27 |     val file = await File::open_read("large_dataset.bin")?
   |                          ^

Use dot syntax (.) instead of double colon (::)

Example: Type.new() instead of Type::new()
```

## examples/06_io/file/file_staging_parallel.spl

- Result: `FAIL`
- Exit code: `1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: compile failed (examples/06_io/file/file_staging_parallel.spl): parse: in "/mnt/data/worktrees/simple-main/examples/06_io/file/file_staging_parallel.spl": Unexpected token: expected expression, found RBrace
```

## examples/06_io/graphics/graphics2d.spl

- Result: `TIMEOUT`
- Exit code: `-1`

### Stderr

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
[33mwarning[0m: Avoid 'export use *' - exposes unnecessary interfaces
  --> /mnt/data/worktrees/simple-main/src/app/io/cli_commands.spl:6:1
   |
  6 | export use app.io._CliCommands.run_commands.*
   | ^

Use explicit exports instead

Example: export use module.{A, B, C} or export A, B from module
```
