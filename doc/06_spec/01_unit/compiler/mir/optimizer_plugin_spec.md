# Optimizer Plugin Specification

> _Unified descriptor + registry generalizing MIR, source, and hotspot optimizers._

<!-- sdn-diagram:id=optimizer_plugin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=optimizer_plugin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

optimizer_plugin_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=optimizer_plugin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimizer Plugin Specification

## Scenarios

### OptimizerPlugin
_Unified descriptor + registry generalizing MIR, source, and hotspot optimizers._

### PluginScope
_PluginScope enum names and inclusion predicates._

#### names Mir scope

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_name(PluginScope.Mir)).to_equal("mir")
```

</details>

#### names Source scope

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_name(PluginScope.Source)).to_equal("source")
```

</details>

#### names Both scope

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_name(PluginScope.Both)).to_equal("both")
```

</details>

#### Mir includes mir

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_includes_mir(PluginScope.Mir)).to_equal(true)
```

</details>

#### Both includes mir

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_includes_mir(PluginScope.Both)).to_equal(true)
```

</details>

#### Source excludes mir

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_includes_mir(PluginScope.Source)).to_equal(false)
```

</details>

#### Source includes source

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_includes_source(PluginScope.Source)).to_equal(true)
```

</details>

#### Both includes source

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_includes_source(PluginScope.Both)).to_equal(true)
```

</details>

#### Mir excludes source

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_scope_includes_source(PluginScope.Mir)).to_equal(false)
```

</details>

### ApplyMode

#### names Static mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_name(ApplyMode.Static)).to_equal("static")
```

</details>

#### names Dynamic mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_name(ApplyMode.Dynamic)).to_equal("dynamic")
```

</details>

#### names Both mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_name(ApplyMode.Both)).to_equal("both")
```

</details>

#### Static includes static

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_includes_static(ApplyMode.Static)).to_equal(true)
```

</details>

#### Both includes static

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_includes_static(ApplyMode.Both)).to_equal(true)
```

</details>

#### Dynamic excludes static

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_includes_static(ApplyMode.Dynamic)).to_equal(false)
```

</details>

#### Dynamic includes dynamic

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_includes_dynamic(ApplyMode.Dynamic)).to_equal(true)
```

</details>

#### Both includes dynamic

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_includes_dynamic(ApplyMode.Both)).to_equal(true)
```

</details>

#### Static excludes dynamic

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_mode_includes_dynamic(ApplyMode.Static)).to_equal(false)
```

</details>

### OptimizerPluginDescriptor

#### creates MIR plugin with correct fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dce = optimizer_plugin_mir(
    "dead_code_elimination", ["dce"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
expect(dce.name).to_equal("dead_code_elimination")
expect(plugin_scope_name(dce.plugin_scope)).to_equal("mir")
expect(apply_mode_name(dce.apply_mode)).to_equal("static")
expect(dce.cost_class).to_equal("cheap")
expect(dce.mir_pass_kind.?).to_equal(true)
expect(dce.source_patterns.len()).to_equal(0)
```

</details>

#### creates source plugin with patterns

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = optimizer_plugin_source(
    "string_concat_loop", [],
    ApplyMode.Static, OptLevel.Speed,
    ["result = result +"]
)
expect(src.name).to_equal("string_concat_loop")
expect(plugin_scope_name(src.plugin_scope)).to_equal("source")
expect(src.cost_class).to_equal("cheap")
expect(src.mir_pass_kind.?).to_equal(false)
expect(src.source_patterns.len()).to_equal(1)
```

</details>

#### creates both-scope plugin

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = optimizer_plugin_both(
    "strength_reduction", ["sr"],
    PassKind.StrengthReduction, PassScope.Function,
    ApplyMode.Both, OptLevel.Speed, "medium",
    ["modulo power of two"]
)
expect(sr.name).to_equal("strength_reduction")
expect(plugin_scope_name(sr.plugin_scope)).to_equal("both")
expect(apply_mode_name(sr.apply_mode)).to_equal("both")
expect(sr.mir_pass_kind.?).to_equal(true)
expect(sr.source_patterns.len()).to_equal(1)
```

</details>

#### matches by name and alias

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dce = optimizer_plugin_mir(
    "dead_code_elimination", ["dce"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
expect(optimizer_plugin_matches_name(dce, "dead_code_elimination")).to_equal(true)
expect(optimizer_plugin_matches_name(dce, "dce")).to_equal(true)
expect(optimizer_plugin_matches_name(dce, "unknown")).to_equal(false)
```

</details>

### cost budget

#### ranks cost classes in order

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(plugin_cost_rank("free")).to_equal(0)
expect(plugin_cost_rank("cheap")).to_equal(1)
expect(plugin_cost_rank("medium")).to_equal(2)
expect(plugin_cost_rank("moderate")).to_equal(3)
expect(plugin_cost_rank("expensive")).to_equal(4)
```

</details>

#### ranks unknown as highest

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unknown_rank = plugin_cost_rank("unknown")
val expensive_rank = plugin_cost_rank("expensive")
expect(unknown_rank).to_equal(5)
expect(unknown_rank).to_be_greater_than(expensive_rank)
```

</details>

### OptimizerPluginRegistry

#### starts empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = optimizer_plugin_registry_new()
expect(optimizer_plugin_registry_count(reg)).to_equal(0)
```

</details>

#### registers and looks up by name

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register
   - Expected: optimizer_plugin_registry_count(reg) equals `1`
   - Expected: found.? is true
   - Expected: found_val.name equals `dead_code_elimination`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val dce = optimizer_plugin_mir(
    "dead_code_elimination", ["dce"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
reg = optimizer_plugin_registry_register(reg, dce)
expect(optimizer_plugin_registry_count(reg)).to_equal(1)
val found = optimizer_plugin_registry_lookup(reg, "dead_code_elimination")
expect(found.?).to_equal(true)
val found_val = found.unwrap()
expect(found_val.name).to_equal("dead_code_elimination")
```

</details>

#### looks up by alias

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register
   - Expected: found.? is true
   - Expected: found_val.name equals `dead_code_elimination`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val dce = optimizer_plugin_mir(
    "dead_code_elimination", ["dce"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
reg = optimizer_plugin_registry_register(reg, dce)
val found = optimizer_plugin_registry_lookup(reg, "dce")
expect(found.?).to_equal(true)
val found_val = found.unwrap()
expect(found_val.name).to_equal("dead_code_elimination")
```

</details>

#### returns nil for unknown name

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = optimizer_plugin_registry_new()
val found = optimizer_plugin_registry_lookup(reg, "nonexistent")
expect(found.?).to_equal(false)
```

</details>

#### filters by Mir scope

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register
   - Expected: mir_plugins.len() equals `1`
   - Expected: first.name equals `dce`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val dce = optimizer_plugin_mir(
    "dce", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val src = optimizer_plugin_source(
    "src_check", [], ApplyMode.Static, OptLevel.Speed,
    ["concat in loop"]
)
reg = optimizer_plugin_registry_register(reg, dce)
reg = optimizer_plugin_registry_register(reg, src)
val mir_plugins = optimizer_plugin_registry_by_scope(reg, PluginScope.Mir)
expect(mir_plugins.len()).to_equal(1)
val first = mir_plugins[0]
expect(first.name).to_equal("dce")
```

</details>

#### filters by Source scope

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register
   - Expected: src_plugins.len() equals `1`
   - Expected: first.name equals `src_check`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val dce = optimizer_plugin_mir(
    "dce", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val src = optimizer_plugin_source(
    "src_check", [], ApplyMode.Static, OptLevel.Speed,
    ["concat in loop"]
)
reg = optimizer_plugin_registry_register(reg, dce)
reg = optimizer_plugin_registry_register(reg, src)
val src_plugins = optimizer_plugin_registry_by_scope(reg, PluginScope.Source)
expect(src_plugins.len()).to_equal(1)
val first = src_plugins[0]
expect(first.name).to_equal("src_check")
```

</details>

#### Both-scope plugin appears in Mir filter

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register
   - Expected: mir_plugins.len() equals `1`
   - Expected: src_plugins.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val both_plugin = optimizer_plugin_both(
    "sr", [], PassKind.StrengthReduction, PassScope.Function,
    ApplyMode.Both, OptLevel.Speed, "medium", ["modulo"]
)
reg = optimizer_plugin_registry_register(reg, both_plugin)
val mir_plugins = optimizer_plugin_registry_by_scope(reg, PluginScope.Mir)
expect(mir_plugins.len()).to_equal(1)
val src_plugins = optimizer_plugin_registry_by_scope(reg, PluginScope.Source)
expect(src_plugins.len()).to_equal(1)
```

</details>

#### filters by Static apply mode

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register
   - Expected: static_plugins.len() equals `1`
   - Expected: first.name equals `static_pass`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val s = optimizer_plugin_mir(
    "static_pass", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val d = optimizer_plugin_mir(
    "dynamic_pass", [], PassKind.ConstantFolding, PassScope.Function,
    ApplyMode.Dynamic, OptLevel.Speed, "medium"
)
reg = optimizer_plugin_registry_register(reg, s)
reg = optimizer_plugin_registry_register(reg, d)
val static_plugins = optimizer_plugin_registry_by_apply_mode(reg, ApplyMode.Static)
expect(static_plugins.len()).to_equal(1)
val first = static_plugins[0]
expect(first.name).to_equal("static_pass")
```

</details>

#### filters by Dynamic apply mode

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register
   - Expected: dyn_plugins.len() equals `1`
   - Expected: first.name equals `dynamic_pass`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val s = optimizer_plugin_mir(
    "static_pass", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val d = optimizer_plugin_mir(
    "dynamic_pass", [], PassKind.ConstantFolding, PassScope.Function,
    ApplyMode.Dynamic, OptLevel.Speed, "medium"
)
reg = optimizer_plugin_registry_register(reg, s)
reg = optimizer_plugin_registry_register(reg, d)
val dyn_plugins = optimizer_plugin_registry_by_apply_mode(reg, ApplyMode.Dynamic)
expect(dyn_plugins.len()).to_equal(1)
val first = dyn_plugins[0]
expect(first.name).to_equal("dynamic_pass")
```

</details>

#### Both-mode plugin appears in both Static and Dynamic filters

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register
   - Expected: s_plugins.len() equals `1`
   - Expected: d_plugins.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val b = optimizer_plugin_mir(
    "both_mode", [], PassKind.StrengthReduction, PassScope.Function,
    ApplyMode.Both, OptLevel.Speed, "medium"
)
reg = optimizer_plugin_registry_register(reg, b)
val s_plugins = optimizer_plugin_registry_by_apply_mode(reg, ApplyMode.Static)
expect(s_plugins.len()).to_equal(1)
val d_plugins = optimizer_plugin_registry_by_apply_mode(reg, ApplyMode.Dynamic)
expect(d_plugins.len()).to_equal(1)
```

</details>

#### filters by cost budget

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register
   - Expected: budget_plugins.len() equals `1`
   - Expected: first.name equals `cheap_pass`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val cheap = optimizer_plugin_mir(
    "cheap_pass", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val expensive = optimizer_plugin_mir(
    "expensive_pass", [], PassKind.AutoVectorize, PassScope.Module,
    ApplyMode.Static, OptLevel.Aggressive, "expensive"
)
reg = optimizer_plugin_registry_register(reg, cheap)
reg = optimizer_plugin_registry_register(reg, expensive)
val budget_plugins = optimizer_plugin_registry_by_cost_budget(reg, "medium")
expect(budget_plugins.len()).to_equal(1)
val first = budget_plugins[0]
expect(first.name).to_equal("cheap_pass")
```

</details>

#### lists all registered names

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register
   - Expected: names.len() equals `2`
   - Expected: names[0] equals `pass_a`
   - Expected: names[1] equals `pass_b`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val a = optimizer_plugin_mir(
    "pass_a", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val b = optimizer_plugin_source(
    "pass_b", [], ApplyMode.Static, OptLevel.Speed, ["pattern"]
)
reg = optimizer_plugin_registry_register(reg, a)
reg = optimizer_plugin_registry_register(reg, b)
val names = optimizer_plugin_registry_names(reg)
expect(names.len()).to_equal(2)
expect(names[0]).to_equal("pass_a")
expect(names[1]).to_equal("pass_b")
```

</details>

### source analysis

#### finds pattern in source lines

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plugin = optimizer_plugin_source(
    "concat_check", [], ApplyMode.Static, OptLevel.Speed,
    ["result = result +"]
)
val lines = ["val x = 1", "result = result + text", "val y = 2"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(1)
expect(suggestions[0].contains("line 2")).to_equal(true)
expect(suggestions[0].contains("result = result +")).to_equal(true)
```

</details>

#### returns empty when no patterns match

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plugin = optimizer_plugin_source(
    "concat_check", [], ApplyMode.Static, OptLevel.Speed,
    ["result = result +"]
)
val lines = ["val x = 1", "val y = 2"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(0)
```

</details>

#### returns empty for mir-only plugin

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plugin = optimizer_plugin_mir(
    "dce", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val lines = ["result = result + text"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(0)
```

</details>

#### finds multiple patterns across lines

1. ["result = result +", " len
   - Expected: suggestions.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plugin = optimizer_plugin_source(
    "multi_check", [], ApplyMode.Static, OptLevel.Speed,
    ["result = result +", ".len()"]
)
val lines = ["for x in items:", "result = result + text", "val n = items.len()"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(2)
```

</details>

### combined registry queries

#### filters scope then apply mode

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register

4. reg = optimizer plugin registry register
   - Expected: mir_plugins.len() equals `2`

5. OptimizerPluginRegistry
   - Expected: static_mir.len() equals `1`
   - Expected: first.name equals `dce`


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val mir_static = optimizer_plugin_mir(
    "dce", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val mir_dynamic = optimizer_plugin_mir(
    "hotspot_inline", [], PassKind.InlineFunctions, PassScope.Module,
    ApplyMode.Dynamic, OptLevel.Aggressive, "expensive"
)
val src_static = optimizer_plugin_source(
    "lint_concat", [], ApplyMode.Static, OptLevel.Speed,
    ["string concat"]
)
reg = optimizer_plugin_registry_register(reg, mir_static)
reg = optimizer_plugin_registry_register(reg, mir_dynamic)
reg = optimizer_plugin_registry_register(reg, src_static)
val mir_plugins = optimizer_plugin_registry_by_scope(reg, PluginScope.Mir)
expect(mir_plugins.len()).to_equal(2)
val static_mir = optimizer_plugin_registry_by_apply_mode(
    OptimizerPluginRegistry(plugins: mir_plugins), ApplyMode.Static
)
expect(static_mir.len()).to_equal(1)
val first = static_mir[0]
expect(first.name).to_equal("dce")
```

</details>

#### budget filter works across scopes

1. var reg = optimizer plugin registry new

2. reg = optimizer plugin registry register

3. reg = optimizer plugin registry register

4. reg = optimizer plugin registry register
   - Expected: budget.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = optimizer_plugin_registry_new()
val cheap_mir = optimizer_plugin_mir(
    "dce", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val cheap_src = optimizer_plugin_source(
    "lint", [], ApplyMode.Static, OptLevel.Speed, ["concat"]
)
val expensive_mir = optimizer_plugin_mir(
    "vectorize", [], PassKind.AutoVectorize, PassScope.Module,
    ApplyMode.Static, OptLevel.Aggressive, "expensive"
)
reg = optimizer_plugin_registry_register(reg, cheap_mir)
reg = optimizer_plugin_registry_register(reg, cheap_src)
reg = optimizer_plugin_registry_register(reg, expensive_mir)
val budget = optimizer_plugin_registry_by_cost_budget(reg, "cheap")
expect(budget.len()).to_equal(2)
```

</details>

### MIR routing adapter
_Plugin adapter routes through run_typed_pass_on_function/module._

#### nil-guard returns function unchanged for source plugin

1. kind: MirInstKind Const

2. id: BlockId

3. terminator: MirTerminator Ret

4. locals = locals push

5. symbol: SymbolId new

6. locals: locals, blocks: [entry], entry block: BlockId new
   - Expected: result.name equals `nilguard_fn`
   - Expected: result.blocks.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_type = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ret_type, is_variadic: false)
val const_inst = MirInst(
    kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(42), ret_type),
    span: nil
)
val entry = MirBlock(
    id: BlockId(id: 0), label: Some("bb0"),
    instructions: [const_inst],
    terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))))
)
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ret_type, kind: LocalKind.Temp, name: nil))
val func = MirFunction(
    symbol: SymbolId.new(0), name: "nilguard_fn", signature: sig,
    locals: locals, blocks: [entry], entry_block: BlockId.new(0),
    span: nil, generic_params: [], is_generic_template: false,
    specialization_of: nil, type_bindings: {}
)
val src_plugin = optimizer_plugin_source(
    "string_concat", [], ApplyMode.Static, OptLevel.Speed, ["concat"]
)
val result = optimizer_plugin_run_on_function(src_plugin, func)
expect(result.name).to_equal("nilguard_fn")
expect(result.blocks.len()).to_equal(1)
```

</details>

#### MIR plugin routes through run_typed_pass_on_module

1. kind: MirInstKind Const

2. id: BlockId

3. terminator: MirTerminator Ret

4. locals = locals push

5. symbol: SymbolId new

6. locals: locals, blocks: [entry], entry block: BlockId new

7. functions[SymbolId new
   - Expected: result.name equals `route_module`


<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_type = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ret_type, is_variadic: false)
val const_inst = MirInst(
    kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(42), ret_type),
    span: nil
)
val entry = MirBlock(
    id: BlockId(id: 0), label: Some("bb0"),
    instructions: [const_inst],
    terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))))
)
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ret_type, kind: LocalKind.Temp, name: nil))
val func = MirFunction(
    symbol: SymbolId.new(0), name: "route_fn", signature: sig,
    locals: locals, blocks: [entry], entry_block: BlockId.new(0),
    span: nil, generic_params: [], is_generic_template: false,
    specialization_of: nil, type_bindings: {}
)
var functions: Dict<SymbolId, MirFunction> = {}
functions[SymbolId.new(0)] = func
val module = MirModule(
    name: "route_module", functions: functions,
    statics: {}, constants: {}, types: {}
)
val mir_plugin = optimizer_plugin_mir(
    "pattern_idiom", [],
    PassKind.PatternIdiom, PassScope.Module,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val result = optimizer_plugin_run_on_module(mir_plugin, module)
expect(result.name).to_equal("route_module")
```

</details>

#### plugin adapter parity with direct run_typed_pass_on_module

1. kind: MirInstKind Const

2. id: BlockId

3. terminator: MirTerminator Ret

4. locals = locals push

5. symbol: SymbolId new

6. locals: locals, blocks: [entry], entry block: BlockId new

7. functions[SymbolId new
   - Expected: direct.name equals `via_plugin.name`


<details>
<summary>Executable SPipe</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_type = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ret_type, is_variadic: false)
val const_inst = MirInst(
    kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(99), ret_type),
    span: nil
)
val entry = MirBlock(
    id: BlockId(id: 0), label: Some("bb0"),
    instructions: [const_inst],
    terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))))
)
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ret_type, kind: LocalKind.Temp, name: nil))
val func = MirFunction(
    symbol: SymbolId.new(0), name: "parity_fn", signature: sig,
    locals: locals, blocks: [entry], entry_block: BlockId.new(0),
    span: nil, generic_params: [], is_generic_template: false,
    specialization_of: nil, type_bindings: {}
)
var functions: Dict<SymbolId, MirFunction> = {}
functions[SymbolId.new(0)] = func
val module = MirModule(
    name: "parity_module", functions: functions,
    statics: {}, constants: {}, types: {}
)
val mir_plugin = optimizer_plugin_mir(
    "pattern_idiom", [],
    PassKind.PatternIdiom, PassScope.Module,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val direct = run_typed_pass_on_module(PassKind.PatternIdiom, module)
val via_plugin = optimizer_plugin_run_on_module(mir_plugin, module)
expect(direct.name).to_equal(via_plugin.name)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/optimizer_plugin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OptimizerPlugin
- PluginScope
- ApplyMode
- OptimizerPluginDescriptor
- cost budget
- OptimizerPluginRegistry
- source analysis
- combined registry queries
- MIR routing adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
