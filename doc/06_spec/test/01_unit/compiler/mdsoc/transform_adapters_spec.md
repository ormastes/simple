# Transform Adapters Specification

> <details>

<!-- sdn-diagram:id=transform_adapters_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transform_adapters_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transform_adapters_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transform_adapters_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transform Adapters Specification

## Scenarios

### TypedAstContext

#### constructs empty context via static factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext.empty()
expect(ctx.ast_decl_count).to_equal(0)
expect(ctx.symbol_count).to_equal(0)
expect(ctx.inferred_type_count).to_equal(0)
```

</details>

#### empty context has no types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext.empty()
expect(ctx.has_types()).to_equal(false)
```

</details>

#### empty context has no symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext.empty()
expect(ctx.has_symbols()).to_equal(false)
```

</details>

#### empty module name is empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext.empty()
expect(ctx.module_name).to_equal("")
```

</details>

#### constructs with data and detects types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext(
    ast_decl_count: 5,
    symbol_count: 3,
    inferred_type_count: 8,
    module_name: "test"
)
expect(ctx.has_types()).to_equal(true)
```

</details>

#### constructs with data and detects symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext(
    ast_decl_count: 5,
    symbol_count: 3,
    inferred_type_count: 8,
    module_name: "test"
)
expect(ctx.has_symbols()).to_equal(true)
```

</details>

#### stores module name

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext(
    ast_decl_count: 5,
    symbol_count: 3,
    inferred_type_count: 8,
    module_name: "test"
)
expect(ctx.module_name).to_equal("test")
```

</details>

#### stores decl count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext(
    ast_decl_count: 5,
    symbol_count: 3,
    inferred_type_count: 8,
    module_name: "test"
)
expect(ctx.ast_decl_count).to_equal(5)
```

</details>

#### zero inferred types means no types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext(
    ast_decl_count: 2,
    symbol_count: 0,
    inferred_type_count: 0,
    module_name: "empty_types"
)
expect(ctx.has_types()).to_equal(false)
```

</details>

#### zero symbols means no symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TypedAstContext(
    ast_decl_count: 2,
    symbol_count: 0,
    inferred_type_count: 5,
    module_name: "no_syms"
)
expect(ctx.has_symbols()).to_equal(false)
```

</details>

### CfgContext

#### creates context for function via static factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext.for_function("main")
expect(ctx.current_fn_name).to_equal("main")
```

</details>

<details>
<summary>Advanced: for_function starts with zero loop depth</summary>

#### for_function starts with zero loop depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext.for_function("main")
expect(ctx.loop_depth).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: for_function is not in loop</summary>

#### for_function is not in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext.for_function("main")
expect(ctx.in_loop()).to_equal(false)
```

</details>


</details>

#### for_function sets entry block label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext.for_function("main")
expect(ctx.current_block_label).to_equal("entry")
```

</details>

#### for_function has empty break stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext.for_function("main")
expect(ctx.current_break_label()).to_equal("")
```

</details>

#### for_function has empty continue stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext.for_function("main")
expect(ctx.current_continue_label()).to_equal("")
```

</details>

<details>
<summary>Advanced: constructs with loop depth</summary>

#### constructs with loop depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext(
    current_fn_name: "foo",
    loop_depth: 2,
    current_block_label: "loop_body",
    break_label_stack: ["loop_end_0", "loop_end_1"],
    continue_label_stack: ["loop_start_0", "loop_start_1"]
)
expect(ctx.in_loop()).to_equal(true)
expect(ctx.loop_depth).to_equal(2)
```

</details>


</details>

#### reports current break label from stack top

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext(
    current_fn_name: "foo",
    loop_depth: 2,
    current_block_label: "loop_body",
    break_label_stack: ["loop_end_0", "loop_end_1"],
    continue_label_stack: ["loop_start_0", "loop_start_1"]
)
expect(ctx.current_break_label()).to_equal("loop_end_1")
```

</details>

#### reports current continue label from stack top

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext(
    current_fn_name: "foo",
    loop_depth: 2,
    current_block_label: "loop_body",
    break_label_stack: ["loop_end_0", "loop_end_1"],
    continue_label_stack: ["loop_start_0", "loop_start_1"]
)
expect(ctx.current_continue_label()).to_equal("loop_start_1")
```

</details>

<details>
<summary>Advanced: loop_depth 1 is in loop</summary>

#### loop_depth 1 is in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext(
    current_fn_name: "bar",
    loop_depth: 1,
    current_block_label: "loop_body",
    break_label_stack: ["end"],
    continue_label_stack: ["start"]
)
expect(ctx.in_loop()).to_equal(true)
```

</details>


</details>

#### stores function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = CfgContext.for_function("process_items")
expect(ctx.current_fn_name).to_equal("process_items")
```

</details>

### MirProgram

#### creates empty program via static factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram.empty()
expect(prog.function_count).to_equal(0)
```

</details>

#### empty program has no functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram.empty()
expect(prog.has_functions()).to_equal(false)
```

</details>

#### empty program has no extern fns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram.empty()
expect(prog.has_extern_fns()).to_equal(false)
```

</details>

#### empty program uses interpreter target triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram.empty()
expect(prog.target_triple).to_equal("interpreter-simple-runtime")
```

</details>

#### empty program has zero string literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram.empty()
expect(prog.string_literal_count).to_equal(0)
```

</details>

#### constructs with functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram(
    function_count: 2,
    extern_fn_names: [],
    string_literal_count: 0,
    target_triple: "x86_64-linux-gnu"
)
expect(prog.has_functions()).to_equal(true)
expect(prog.function_count).to_equal(2)
```

</details>

#### constructs with extern functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram(
    function_count: 2,
    extern_fn_names: ["printf", "malloc"],
    string_literal_count: 3,
    target_triple: "x86_64-linux-gnu"
)
expect(prog.has_extern_fns()).to_equal(true)
```

</details>

#### stores target triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram(
    function_count: 1,
    extern_fn_names: [],
    string_literal_count: 0,
    target_triple: "aarch64-linux-gnu"
)
expect(prog.target_triple).to_equal("aarch64-linux-gnu")
```

</details>

#### stores string literal count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram(
    function_count: 1,
    extern_fn_names: [],
    string_literal_count: 7,
    target_triple: "x86_64-linux-gnu"
)
expect(prog.string_literal_count).to_equal(7)
```

</details>

#### no functions returns false for has_functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram(
    function_count: 0,
    extern_fn_names: [],
    string_literal_count: 0,
    target_triple: "x86_64-linux-gnu"
)
expect(prog.has_functions()).to_equal(false)
```

</details>

#### empty extern names returns false for has_extern_fns

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prog = MirProgram(
    function_count: 1,
    extern_fn_names: [],
    string_literal_count: 0,
    target_triple: "x86_64-linux-gnu"
)
expect(prog.has_extern_fns()).to_equal(false)
```

</details>

### MirDebugInfo

#### constructs with source file info

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dbg = MirDebugInfo(
    fn_source_files: ["main.spl", "lib.spl"],
    fn_start_lines: [1, 10]
)
expect(dbg.fn_start_lines[0]).to_equal(1)
expect(dbg.fn_start_lines[1]).to_equal(10)
```

</details>

#### constructs with empty debug info

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dbg = MirDebugInfo(
    fn_source_files: [],
    fn_start_lines: []
)
expect(dbg.fn_source_files.len()).to_equal(0)
```

</details>

### TokenStreamView

#### constructs via static factory from_lexer_output

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output(
    [1, 2, 3],
    ["fn", "main", "("],
    [1, 1, 1],
    [0, 3, 7],
    3,
    "fn main("
)
expect(view.token_count).to_equal(3)
expect(view.source_text).to_equal("fn main(")
```

</details>

#### is_empty returns true when token_count is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView(
    token_tags: [],
    token_texts: [],
    token_lines: [],
    token_cols: [],
    token_count: 0,
    source_text: ""
)
expect(view.is_empty()).to_equal(true)
```

</details>

#### is_empty returns false when token_count is nonzero

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output(
    [1],
    ["fn"],
    [1],
    [0],
    1,
    "fn"
)
expect(view.is_empty()).to_equal(false)
```

</details>

#### get_token_text returns correct text for valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output(
    [1, 2, 3],
    ["fn", "main", "("],
    [1, 1, 1],
    [0, 3, 7],
    3,
    "fn main("
)
expect(view.get_token_text(0)).to_equal("fn")
expect(view.get_token_text(1)).to_equal("main")
expect(view.get_token_text(2)).to_equal("(")
```

</details>

#### get_token_text returns empty string for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output(
    [1, 2],
    ["fn", "main"],
    [1, 1],
    [0, 3],
    2,
    "fn main"
)
expect(view.get_token_text(-1)).to_equal("")
```

</details>

#### get_token_text returns empty string for index at token_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output(
    [1, 2],
    ["fn", "main"],
    [1, 1],
    [0, 3],
    2,
    "fn main"
)
expect(view.get_token_text(2)).to_equal("")
```

</details>

#### get_token_text returns empty string for index beyond token_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output(
    [1],
    ["fn"],
    [1],
    [0],
    1,
    "fn"
)
expect(view.get_token_text(99)).to_equal("")
```

</details>

#### stores source_text via factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output(
    [],
    [],
    [],
    [],
    0,
    "val x = 1"
)
expect(view.source_text).to_equal("val x = 1")
```

</details>

#### empty view has zero token_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = TokenStreamView.from_lexer_output([], [], [], [], 0, "")
expect(view.token_count).to_equal(0)
```

</details>

### MirOptView

#### creates empty view with optimization level

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView.empty(2)
expect(view.mir_fn_count).to_equal(0)
expect(view.optimization_level).to_equal(2)
```

</details>

#### empty view has no functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView.empty(1)
expect(view.has_functions()).to_equal(false)
```

</details>

#### empty view is not optimized at level 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView.empty(0)
expect(view.is_optimized()).to_equal(false)
```

</details>

#### empty view is optimized at level 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView.empty(1)
expect(view.is_optimized()).to_equal(true)
```

</details>

#### constructs with functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView(
    mir_fn_count: 5,
    mir_inst_count: 80,
    optimization_level: 2
)
expect(view.has_functions()).to_equal(true)
expect(view.mir_fn_count).to_equal(5)
```

</details>

#### average_insts_per_fn computes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView(
    mir_fn_count: 4,
    mir_inst_count: 100,
    optimization_level: 1
)
expect(view.average_insts_per_fn()).to_equal(25)
```

</details>

#### average_insts_per_fn returns 0 for empty view

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView.empty(1)
expect(view.average_insts_per_fn()).to_equal(0)
```

</details>

#### stores instruction count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = MirOptView(
    mir_fn_count: 2,
    mir_inst_count: 30,
    optimization_level: 3
)
expect(view.mir_inst_count).to_equal(30)
```

</details>

### ObjectFileView

#### creates failed view

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView.failed("x86_64-linux-gnu")
expect(view.success).to_equal(false)
expect(view.object_byte_count).to_equal(0)
```

</details>

#### failed view is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView.failed("x86_64-linux-gnu")
expect(view.is_empty()).to_equal(true)
```

</details>

#### failed view has no symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView.failed("x86_64-linux-gnu")
expect(view.has_symbols()).to_equal(false)
```

</details>

#### creates view from codegen output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView.from_codegen(4096, 8, "x86_64-linux-gnu")
expect(view.success).to_equal(true)
expect(view.object_byte_count).to_equal(4096)
expect(view.symbol_count).to_equal(8)
```

</details>

#### codegen view is not empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView.from_codegen(1024, 3, "aarch64-linux-gnu")
expect(view.is_empty()).to_equal(false)
```

</details>

#### codegen view has symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView.from_codegen(2048, 5, "x86_64-linux-gnu")
expect(view.has_symbols()).to_equal(true)
```

</details>

#### stores target triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView.from_codegen(512, 2, "riscv64-linux-gnu")
expect(view.target_triple).to_equal("riscv64-linux-gnu")
```

</details>

#### constructs directly with zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = ObjectFileView(
    object_byte_count: 0,
    symbol_count: 0,
    target_triple: "x86_64-linux-gnu",
    success: false
)
expect(view.is_empty()).to_equal(true)
```

</details>

### LoadedModuleView

#### creates empty view

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = LoadedModuleView.empty("my_module")
expect(view.module_name).to_equal("my_module")
expect(view.byte_count).to_equal(0)
```

</details>

#### empty view has no source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = LoadedModuleView.empty("test")
expect(view.has_source()).to_equal(false)
```

</details>

#### empty view is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = LoadedModuleView.empty("test")
expect(view.is_empty()).to_equal(true)
```

</details>

#### creates view from source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = LoadedModuleView.from_source("math", "src/math.spl", "fn add(a: i64, b: i64) -> i64: a + b")
expect(view.module_name).to_equal("math")
expect(view.file_path).to_equal("src/math.spl")
```

</details>

#### from_source has source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = LoadedModuleView.from_source("lib", "lib.spl", "val X = 1")
expect(view.has_source()).to_equal(true)
expect(view.is_empty()).to_equal(false)
```

</details>

#### from_source stores byte count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn foo(): 1"
val view = LoadedModuleView.from_source("foo", "foo.spl", src)
expect(view.byte_count).to_equal(src.len())
```

</details>

#### from_source stores source text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = LoadedModuleView.from_source("x", "x.spl", "val x = 42")
expect(view.source_text).to_equal("val x = 42")
```

</details>

#### constructs directly with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = LoadedModuleView(
    module_name: "core",
    source_text: "# core module",
    file_path: "core.spl",
    byte_count: 13
)
expect(view.module_name).to_equal("core")
expect(view.byte_count).to_equal(13)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/transform_adapters_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TypedAstContext
- CfgContext
- MirProgram
- MirDebugInfo
- TokenStreamView
- MirOptView
- ObjectFileView
- LoadedModuleView

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
