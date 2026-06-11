# Feature Ports Specification

> <details>

<!-- sdn-diagram:id=feature_ports_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_ports_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_ports_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_ports_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Ports Specification

## Scenarios

### LexerInputPort

#### constructs with source_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LexerInputPort(source_text: "val x = 1")
expect(port.source_text).to_equal("val x = 1")
```

</details>

#### constructs with empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LexerInputPort(source_text: "")
expect(port.source_text).to_equal("")
```

</details>

#### constructs with multiline source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LexerInputPort(source_text: "fn foo():\n    1")
expect(port.source_text).to_start_with("fn foo")
```

</details>

### LexerOutputPort

#### constructs with token data

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LexerOutputPort(
    token_tags: [1, 2, 3],
    token_texts: ["val", "x", "="],
    token_lines: [1, 1, 1],
    token_cols: [1, 5, 7],
    token_count: 3
)
expect(port.token_count).to_equal(3)
```

</details>

#### constructs with empty token arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LexerOutputPort(
    token_tags: [],
    token_texts: [],
    token_lines: [],
    token_cols: [],
    token_count: 0
)
expect(port.token_count).to_equal(0)
```

</details>

### ParseError

#### constructs with message and location

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ParseError(message: "unexpected token", line: 5, col: 12)
expect(err.message).to_equal("unexpected token")
expect(err.line).to_equal(5)
expect(err.col).to_equal(12)
```

</details>

#### stores zero location for start of file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ParseError(message: "syntax error", line: 1, col: 1)
expect(err.line).to_equal(1)
expect(err.col).to_equal(1)
```

</details>

#### stores large line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ParseError(message: "eof", line: 9999, col: 80)
expect(err.line).to_equal(9999)
```

</details>

### ParserInputPort

#### constructs with token stream data

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = ParserInputPort(
    token_tags: [1, 2],
    token_texts: ["val", "x"],
    token_lines: [1, 1],
    token_cols: [1, 5],
    token_count: 2,
    source_text: "val x"
)
expect(port.token_count).to_equal(2)
```

</details>

### ParserOutputPort

#### constructs empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = ParserOutputPort(
    expr_count: 0,
    stmt_count: 0,
    decl_count: 0,
    root_decls: [],
    errors: [],
    error_count: 0
)
expect(port.error_count).to_equal(0)
```

</details>

#### constructs output with counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = ParserOutputPort(
    expr_count: 10,
    stmt_count: 5,
    decl_count: 3,
    root_decls: [0, 1, 2],
    errors: [],
    error_count: 0
)
expect(port.expr_count).to_equal(10)
expect(port.stmt_count).to_equal(5)
expect(port.decl_count).to_equal(3)
```

</details>

### DesugarInputPort

#### constructs with source and module name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = DesugarInputPort(source_text: "fn foo(): 1", module_name: "test")
expect(port.module_name).to_equal("test")
expect(port.source_text).to_equal("fn foo(): 1")
```

</details>

#### holds the module name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = DesugarInputPort(source_text: "", module_name: "my_module")
expect(port.module_name).to_equal("my_module")
```

</details>

### DesugarOutputPort

#### constructs with desugared source

1. desugared source: "fn foo
   - Expected: port.pass_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = DesugarOutputPort(
    desugared_source: "fn foo(): 1",
    injected_fn_names: [],
    pass_count: 5
)
expect(port.pass_count).to_equal(5)
```

</details>

#### constructs with injected function names

1. desugared source: "fn foo
   - Expected: port.pass_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = DesugarOutputPort(
    desugared_source: "fn foo(): 1\nfn __foo_impl(): 1",
    injected_fn_names: ["__foo_impl"],
    pass_count: 5
)
expect(port.pass_count).to_equal(5)
```

</details>

### CodegenInputPort

#### constructs with function counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = CodegenInputPort(
    function_count: 3,
    extern_fn_count: 1,
    string_literal_count: 2
)
expect(port.function_count).to_equal(3)
expect(port.extern_fn_count).to_equal(1)
expect(port.string_literal_count).to_equal(2)
```

</details>

#### constructs with zero counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = CodegenInputPort(
    function_count: 0,
    extern_fn_count: 0,
    string_literal_count: 0
)
expect(port.function_count).to_equal(0)
```

</details>

### CodegenOutputPort

#### reports success

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = CodegenOutputPort(
    object_byte_count: 1024,
    symbol_count: 5,
    target_triple: "x86_64-linux-gnu",
    success: true
)
expect(port.success).to_equal(true)
expect(port.target_triple).to_equal("x86_64-linux-gnu")
```

</details>

#### reports failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = CodegenOutputPort(
    object_byte_count: 0,
    symbol_count: 0,
    target_triple: "x86_64-linux-gnu",
    success: false
)
expect(port.success).to_equal(false)
```

</details>

#### stores object byte count

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = CodegenOutputPort(
    object_byte_count: 4096,
    symbol_count: 10,
    target_triple: "aarch64-linux-gnu",
    success: true
)
expect(port.object_byte_count).to_equal(4096)
expect(port.symbol_count).to_equal(10)
```

</details>

### MonomorphizeInputPort

#### constructs with generic function count

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = MonomorphizeInputPort(
    typed_decl_count: 10,
    generic_fn_count: 3,
    has_generics: true
)
expect(port.typed_decl_count).to_equal(10)
expect(port.generic_fn_count).to_equal(3)
expect(port.has_generics).to_equal(true)
```

</details>

#### constructs with no generics

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = MonomorphizeInputPort(
    typed_decl_count: 5,
    generic_fn_count: 0,
    has_generics: false
)
expect(port.generic_fn_count).to_equal(0)
expect(port.has_generics).to_equal(false)
```

</details>

#### stores typed declaration count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = MonomorphizeInputPort(
    typed_decl_count: 42,
    generic_fn_count: 7,
    has_generics: true
)
expect(port.typed_decl_count).to_equal(42)
```

</details>

### MonomorphizeOutputPort

#### constructs with specialization counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = MonomorphizeOutputPort(
    mono_decl_count: 15,
    specialized_count: 6
)
expect(port.mono_decl_count).to_equal(15)
expect(port.specialized_count).to_equal(6)
```

</details>

#### constructs with zero specializations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = MonomorphizeOutputPort(
    mono_decl_count: 5,
    specialized_count: 0
)
expect(port.specialized_count).to_equal(0)
```

</details>

### OptimizeInputPort

#### constructs with basic optimization level

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = OptimizeInputPort(
    mir_fn_count: 8,
    mir_inst_count: 120,
    optimization_level: 1
)
expect(port.mir_fn_count).to_equal(8)
expect(port.mir_inst_count).to_equal(120)
expect(port.optimization_level).to_equal(1)
```

</details>

#### constructs with no optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = OptimizeInputPort(
    mir_fn_count: 3,
    mir_inst_count: 40,
    optimization_level: 0
)
expect(port.optimization_level).to_equal(0)
```

</details>

#### constructs with aggressive optimization

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = OptimizeInputPort(
    mir_fn_count: 20,
    mir_inst_count: 500,
    optimization_level: 3
)
expect(port.optimization_level).to_equal(3)
expect(port.mir_fn_count).to_equal(20)
```

</details>

### OptimizeOutputPort

#### constructs with eliminated instruction count

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = OptimizeOutputPort(
    mir_fn_count: 8,
    mir_inst_count: 90,
    eliminated_count: 30
)
expect(port.mir_fn_count).to_equal(8)
expect(port.mir_inst_count).to_equal(90)
expect(port.eliminated_count).to_equal(30)
```

</details>

#### constructs with no eliminated instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = OptimizeOutputPort(
    mir_fn_count: 3,
    mir_inst_count: 40,
    eliminated_count: 0
)
expect(port.eliminated_count).to_equal(0)
```

</details>

### LinkerInputPort

#### constructs for executable output

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LinkerInputPort(
    object_file_count: 3,
    library_count: 2,
    output_type: "exe",
    output_path: "/tmp/out"
)
expect(port.object_file_count).to_equal(3)
expect(port.library_count).to_equal(2)
expect(port.output_type).to_equal("exe")
expect(port.output_path).to_equal("/tmp/out")
```

</details>

#### constructs for library output

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LinkerInputPort(
    object_file_count: 1,
    library_count: 0,
    output_type: "lib",
    output_path: "/tmp/libfoo.a"
)
expect(port.output_type).to_equal("lib")
```

</details>

#### constructs for smf output

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LinkerInputPort(
    object_file_count: 2,
    library_count: 1,
    output_type: "smf",
    output_path: "/tmp/mod.smf"
)
expect(port.output_type).to_equal("smf")
expect(port.object_file_count).to_equal(2)
```

</details>

### LinkerOutputPort

#### constructs successful link result

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LinkerOutputPort(
    output_path: "/tmp/out",
    output_size_bytes: 65536,
    success: true,
    error_message: ""
)
expect(port.output_path).to_equal("/tmp/out")
expect(port.output_size_bytes).to_equal(65536)
expect(port.success).to_equal(true)
```

</details>

#### constructs failed link result

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = LinkerOutputPort(
    output_path: "",
    output_size_bytes: 0,
    success: false,
    error_message: "undefined symbol: main"
)
expect(port.success).to_equal(false)
expect(port.error_message).to_equal("undefined symbol: main")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/feature_ports_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LexerInputPort
- LexerOutputPort
- ParseError
- ParserInputPort
- ParserOutputPort
- DesugarInputPort
- DesugarOutputPort
- CodegenInputPort
- CodegenOutputPort
- MonomorphizeInputPort
- MonomorphizeOutputPort
- OptimizeInputPort
- OptimizeOutputPort
- LinkerInputPort
- LinkerOutputPort

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
