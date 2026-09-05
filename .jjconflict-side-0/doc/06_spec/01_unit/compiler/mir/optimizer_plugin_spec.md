# optimizer_plugin_spec

> Purpose: Prove that OptimizerPlugin.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# optimizer_plugin_spec

Purpose: Prove that OptimizerPlugin.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/optimizer_plugin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that OptimizerPlugin.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### OptimizerPlugin

### PluginScope
_PluginScope enum names and inclusion predicates._

#### names Mir scope

- names Mir scope
- Verify: names Mir scope
   - Expected: plugin_scope_name(PluginScope.Mir) equals `mir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names Mir scope")
step("Verify: names Mir scope")
# @req: REQ-COMPILER-MIR-001
expect(plugin_scope_name(PluginScope.Mir)).to_equal("mir")
```

</details>

#### names Source scope

- names Source scope
- Verify: names Source scope
   - Expected: plugin_scope_name(PluginScope.Source) equals `source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names Source scope")
step("Verify: names Source scope")
expect(plugin_scope_name(PluginScope.Source)).to_equal("source")
```

</details>

#### names Both scope

- names Both scope
- Verify: names Both scope
   - Expected: plugin_scope_name(PluginScope.Both) equals `both`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names Both scope")
step("Verify: names Both scope")
expect(plugin_scope_name(PluginScope.Both)).to_equal("both")
```

</details>

#### Mir includes mir

- Mir includes mir
- Verify: Mir includes mir
   - Expected: plugin_scope_includes_mir(PluginScope.Mir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Mir includes mir")
step("Verify: Mir includes mir")
expect(plugin_scope_includes_mir(PluginScope.Mir)).to_equal(true)
```

</details>

#### Both includes mir

- Both includes mir
- Verify: Both includes mir
   - Expected: plugin_scope_includes_mir(PluginScope.Both) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Both includes mir")
step("Verify: Both includes mir")
expect(plugin_scope_includes_mir(PluginScope.Both)).to_equal(true)
```

</details>

#### Source excludes mir

- Source excludes mir
- Verify: Source excludes mir
   - Expected: plugin_scope_includes_mir(PluginScope.Source) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Source excludes mir")
step("Verify: Source excludes mir")
expect(plugin_scope_includes_mir(PluginScope.Source)).to_equal(false)
```

</details>

#### Source includes source

- Source includes source
- Verify: Source includes source
   - Expected: plugin_scope_includes_source(PluginScope.Source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Source includes source")
step("Verify: Source includes source")
expect(plugin_scope_includes_source(PluginScope.Source)).to_equal(true)
```

</details>

#### Both includes source

- Both includes source
- Verify: Both includes source
   - Expected: plugin_scope_includes_source(PluginScope.Both) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Both includes source")
step("Verify: Both includes source")
expect(plugin_scope_includes_source(PluginScope.Both)).to_equal(true)
```

</details>

#### Mir excludes source

- Mir excludes source
- Verify: Mir excludes source
   - Expected: plugin_scope_includes_source(PluginScope.Mir) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Mir excludes source")
step("Verify: Mir excludes source")
expect(plugin_scope_includes_source(PluginScope.Mir)).to_equal(false)
```

</details>

### ApplyMode

#### names Static mode

- names Static mode
- Verify: names Static mode
   - Expected: apply_mode_name(ApplyMode.Static) equals `static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names Static mode")
step("Verify: names Static mode")
expect(apply_mode_name(ApplyMode.Static)).to_equal("static")
```

</details>

#### names Dynamic mode

- names Dynamic mode
- Verify: names Dynamic mode
   - Expected: apply_mode_name(ApplyMode.Dynamic) equals `dynamic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names Dynamic mode")
step("Verify: names Dynamic mode")
expect(apply_mode_name(ApplyMode.Dynamic)).to_equal("dynamic")
```

</details>

#### names Both mode

- names Both mode
- Verify: names Both mode
   - Expected: apply_mode_name(ApplyMode.Both) equals `both`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names Both mode")
step("Verify: names Both mode")
expect(apply_mode_name(ApplyMode.Both)).to_equal("both")
```

</details>

#### Static includes static

- Static includes static
- Verify: Static includes static
   - Expected: apply_mode_includes_static(ApplyMode.Static) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Static includes static")
step("Verify: Static includes static")
expect(apply_mode_includes_static(ApplyMode.Static)).to_equal(true)
```

</details>

#### Both includes static

- Both includes static
- Verify: Both includes static
   - Expected: apply_mode_includes_static(ApplyMode.Both) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Both includes static")
step("Verify: Both includes static")
expect(apply_mode_includes_static(ApplyMode.Both)).to_equal(true)
```

</details>

#### Dynamic excludes static

- Dynamic excludes static
- Verify: Dynamic excludes static
   - Expected: apply_mode_includes_static(ApplyMode.Dynamic) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Dynamic excludes static")
step("Verify: Dynamic excludes static")
expect(apply_mode_includes_static(ApplyMode.Dynamic)).to_equal(false)
```

</details>

#### Dynamic includes dynamic

- Dynamic includes dynamic
- Verify: Dynamic includes dynamic
   - Expected: apply_mode_includes_dynamic(ApplyMode.Dynamic) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Dynamic includes dynamic")
step("Verify: Dynamic includes dynamic")
expect(apply_mode_includes_dynamic(ApplyMode.Dynamic)).to_equal(true)
```

</details>

#### Both includes dynamic

- Both includes dynamic
- Verify: Both includes dynamic
   - Expected: apply_mode_includes_dynamic(ApplyMode.Both) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Both includes dynamic")
step("Verify: Both includes dynamic")
expect(apply_mode_includes_dynamic(ApplyMode.Both)).to_equal(true)
```

</details>

#### Static excludes dynamic

- Static excludes dynamic
- Verify: Static excludes dynamic
   - Expected: apply_mode_includes_dynamic(ApplyMode.Static) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Static excludes dynamic")
step("Verify: Static excludes dynamic")
expect(apply_mode_includes_dynamic(ApplyMode.Static)).to_equal(false)
```

</details>

### OptimizerPluginDescriptor

#### creates MIR plugin with correct fields

- creates MIR plugin with correct fields
- Verify: creates MIR plugin with correct fields
   - Expected: dce.name equals `dead_code_elimination`
   - Expected: plugin_scope_name(dce.plugin_scope) equals `mir`
   - Expected: apply_mode_name(dce.apply_mode) equals `static`
   - Expected: dce.cost_class equals `cheap`
   - Expected: dce.mir_pass_kind != nil is true
   - Expected: dce.source_patterns.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates MIR plugin with correct fields")
step("Verify: creates MIR plugin with correct fields")
val dce = optimizer_plugin_mir(
    "dead_code_elimination", ["dce"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
expect(dce.name).to_equal("dead_code_elimination")
expect(plugin_scope_name(dce.plugin_scope)).to_equal("mir")
expect(apply_mode_name(dce.apply_mode)).to_equal("static")
expect(dce.cost_class).to_equal("cheap")
expect(dce.mir_pass_kind != nil).to_equal(true)
expect(dce.source_patterns.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### creates source plugin with patterns

- creates source plugin with patterns
- Verify: creates source plugin with patterns
   - Expected: src.name equals `string_concat_loop`
   - Expected: plugin_scope_name(src.plugin_scope) equals `source`
   - Expected: src.cost_class equals `cheap`
   - Expected: src.mir_pass_kind != nil is false
   - Expected: src.source_patterns.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates source plugin with patterns")
step("Verify: creates source plugin with patterns")
val src = optimizer_plugin_source(
    "string_concat_loop", [],
    ApplyMode.Static, OptLevel.Speed,
    ["result = result +"]
)
expect(src.name).to_equal("string_concat_loop")
expect(plugin_scope_name(src.plugin_scope)).to_equal("source")
expect(src.cost_class).to_equal("cheap")
expect(src.mir_pass_kind != nil).to_equal(false)
expect(src.source_patterns.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### creates both-scope plugin

- creates both-scope plugin
- Verify: creates both-scope plugin
   - Expected: sr.name equals `strength_reduction`
   - Expected: plugin_scope_name(sr.plugin_scope) equals `both`
   - Expected: apply_mode_name(sr.apply_mode) equals `both`
   - Expected: sr.mir_pass_kind != nil is true
   - Expected: sr.source_patterns.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates both-scope plugin")
step("Verify: creates both-scope plugin")
val sr = optimizer_plugin_both(
    "strength_reduction", ["sr"],
    PassKind.StrengthReduction, PassScope.Function,
    ApplyMode.Both, OptLevel.Speed, "medium",
    ["modulo power of two"]
)
expect(sr.name).to_equal("strength_reduction")
expect(plugin_scope_name(sr.plugin_scope)).to_equal("both")
expect(apply_mode_name(sr.apply_mode)).to_equal("both")
expect(sr.mir_pass_kind != nil).to_equal(true)
expect(sr.source_patterns.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### matches by name and alias

- matches by name and alias
- Verify: matches by name and alias
   - Expected: optimizer_plugin_matches_name(dce, "dead_code_elimination") is true
   - Expected: optimizer_plugin_matches_name(dce, "dce") is true
   - Expected: optimizer_plugin_matches_name(dce, "unknown") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches by name and alias")
step("Verify: matches by name and alias")
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

- ranks cost classes in order
- Verify: ranks cost classes in order
   - Expected: plugin_cost_rank("free") equals `0`
   - Expected: plugin_cost_rank("cheap") equals `1`
   - Expected: plugin_cost_rank("medium") equals `2`
   - Expected: plugin_cost_rank("moderate") equals `3`
   - Expected: plugin_cost_rank("expensive") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ranks cost classes in order")
step("Verify: ranks cost classes in order")
expect(plugin_cost_rank("free")).to_equal(0)
expect(plugin_cost_rank("cheap")).to_equal(1)
expect(plugin_cost_rank("medium")).to_equal(2)
expect(plugin_cost_rank("moderate")).to_equal(3)
expect(plugin_cost_rank("expensive")).to_equal(4)
```

</details>

#### ranks unknown as highest

- ranks unknown as highest
- Verify: ranks unknown as highest
   - Expected: unknown_rank equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ranks unknown as highest")
step("Verify: ranks unknown as highest")
val unknown_rank = plugin_cost_rank("unknown")
val expensive_rank = plugin_cost_rank("expensive")
expect(unknown_rank).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(unknown_rank).to_be_greater_than(expensive_rank)
```

</details>

### OptimizerPluginRegistry

#### starts empty

- starts empty
- Verify: starts empty
   - Expected: optimizer_plugin_registry_count(reg) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("starts empty")
step("Verify: starts empty")
val reg = optimizer_plugin_registry_new()
expect(optimizer_plugin_registry_count(reg)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### registers and looks up by name

- registers and looks up by name
- Verify: registers and looks up by name
   - Expected: optimizer_plugin_registry_count(reg) equals `1`
   - Expected: found != nil is true
   - Expected: found_val.name equals `dead_code_elimination`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers and looks up by name")
step("Verify: registers and looks up by name")
var reg = optimizer_plugin_registry_new()
val dce = optimizer_plugin_mir(
    "dead_code_elimination", ["dce"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
reg = optimizer_plugin_registry_register(reg, dce)
expect(optimizer_plugin_registry_count(reg)).to_equal(1)  # oracle: 1 — named expected value from the requirement
val found = optimizer_plugin_registry_lookup(reg, "dead_code_elimination")
expect(found != nil).to_equal(true)
val found_val = found.unwrap()
expect(found_val.name).to_equal("dead_code_elimination")
```

</details>

#### looks up by alias

- looks up by alias
- Verify: looks up by alias
   - Expected: found != nil is true
   - Expected: found_val.name equals `dead_code_elimination`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("looks up by alias")
step("Verify: looks up by alias")
var reg = optimizer_plugin_registry_new()
val dce = optimizer_plugin_mir(
    "dead_code_elimination", ["dce"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
reg = optimizer_plugin_registry_register(reg, dce)
val found = optimizer_plugin_registry_lookup(reg, "dce")
expect(found != nil).to_equal(true)
val found_val = found.unwrap()
expect(found_val.name).to_equal("dead_code_elimination")
```

</details>

#### returns nil for unknown name

- returns nil for unknown name
- Verify: returns nil for unknown name
   - Expected: found != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns nil for unknown name")
step("Verify: returns nil for unknown name")
val reg = optimizer_plugin_registry_new()
val found = optimizer_plugin_registry_lookup(reg, "nonexistent")
expect(found != nil).to_equal(false)
```

</details>

#### filters by Mir scope

- filters by Mir scope
- Verify: filters by Mir scope
   - Expected: mir_plugins.len() equals `1`
   - Expected: first.name equals `dce`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters by Mir scope")
step("Verify: filters by Mir scope")
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
expect(mir_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val first = mir_plugins[0]
expect(first.name).to_equal("dce")
```

</details>

#### filters by Source scope

- filters by Source scope
- Verify: filters by Source scope
   - Expected: src_plugins.len() equals `1`
   - Expected: first.name equals `src_check`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters by Source scope")
step("Verify: filters by Source scope")
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
expect(src_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val first = src_plugins[0]
expect(first.name).to_equal("src_check")
```

</details>

#### Both-scope plugin appears in Mir filter

- Both-scope plugin appears in Mir filter
- Verify: Both-scope plugin appears in Mir filter
   - Expected: mir_plugins.len() equals `1`
   - Expected: src_plugins.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Both-scope plugin appears in Mir filter")
step("Verify: Both-scope plugin appears in Mir filter")
var reg = optimizer_plugin_registry_new()
val both_plugin = optimizer_plugin_both(
    "sr", [], PassKind.StrengthReduction, PassScope.Function,
    ApplyMode.Both, OptLevel.Speed, "medium", ["modulo"]
)
reg = optimizer_plugin_registry_register(reg, both_plugin)
val mir_plugins = optimizer_plugin_registry_by_scope(reg, PluginScope.Mir)
expect(mir_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val src_plugins = optimizer_plugin_registry_by_scope(reg, PluginScope.Source)
expect(src_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### filters by Static apply mode

- filters by Static apply mode
- Verify: filters by Static apply mode
   - Expected: static_plugins.len() equals `1`
   - Expected: first.name equals `static_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters by Static apply mode")
step("Verify: filters by Static apply mode")
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
expect(static_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val first = static_plugins[0]
expect(first.name).to_equal("static_pass")
```

</details>

#### filters by Dynamic apply mode

- filters by Dynamic apply mode
- Verify: filters by Dynamic apply mode
   - Expected: dyn_plugins.len() equals `1`
   - Expected: first.name equals `dynamic_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters by Dynamic apply mode")
step("Verify: filters by Dynamic apply mode")
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
expect(dyn_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val first = dyn_plugins[0]
expect(first.name).to_equal("dynamic_pass")
```

</details>

#### Both-mode plugin appears in both Static and Dynamic filters

- Both-mode plugin appears in both Static and Dynamic filters
- Verify: Both-mode plugin appears in both Static and Dynamic filters
   - Expected: s_plugins.len() equals `1`
   - Expected: d_plugins.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Both-mode plugin appears in both Static and Dynamic filters")
step("Verify: Both-mode plugin appears in both Static and Dynamic filters")
var reg = optimizer_plugin_registry_new()
val b = optimizer_plugin_mir(
    "both_mode", [], PassKind.StrengthReduction, PassScope.Function,
    ApplyMode.Both, OptLevel.Speed, "medium"
)
reg = optimizer_plugin_registry_register(reg, b)
val s_plugins = optimizer_plugin_registry_by_apply_mode(reg, ApplyMode.Static)
expect(s_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val d_plugins = optimizer_plugin_registry_by_apply_mode(reg, ApplyMode.Dynamic)
expect(d_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### filters by cost budget

- filters by cost budget
- Verify: filters by cost budget
   - Expected: budget_plugins.len() equals `1`
   - Expected: first.name equals `cheap_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters by cost budget")
step("Verify: filters by cost budget")
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
expect(budget_plugins.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val first = budget_plugins[0]
expect(first.name).to_equal("cheap_pass")
```

</details>

#### lists all registered names

- lists all registered names
- Verify: lists all registered names
   - Expected: names.len() equals `2`
   - Expected: names[0] equals `pass_a`
   - Expected: names[1] equals `pass_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lists all registered names")
step("Verify: lists all registered names")
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
expect(names.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(names[0]).to_equal("pass_a")
expect(names[1]).to_equal("pass_b")
```

</details>

### source analysis

#### finds pattern in source lines

- finds pattern in source lines
- Verify: finds pattern in source lines
   - Expected: suggestions.len() equals `1`
   - Expected: suggestions[0] contains `line 2`
   - Expected: suggestions[0] contains `result = result +`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds pattern in source lines")
step("Verify: finds pattern in source lines")
val plugin = optimizer_plugin_source(
    "concat_check", [], ApplyMode.Static, OptLevel.Speed,
    ["result = result +"]
)
val lines = ["val x = 1", "result = result + text", "val y = 2"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(suggestions[0].contains("line 2")).to_equal(true)
expect(suggestions[0].contains("result = result +")).to_equal(true)
```

</details>

#### returns empty when no patterns match

- returns empty when no patterns match
- Verify: returns empty when no patterns match
   - Expected: suggestions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty when no patterns match")
step("Verify: returns empty when no patterns match")
val plugin = optimizer_plugin_source(
    "concat_check", [], ApplyMode.Static, OptLevel.Speed,
    ["result = result +"]
)
val lines = ["val x = 1", "val y = 2"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns empty for mir-only plugin

- returns empty for mir-only plugin
- Verify: returns empty for mir-only plugin
   - Expected: suggestions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty for mir-only plugin")
step("Verify: returns empty for mir-only plugin")
val plugin = optimizer_plugin_mir(
    "dce", [], PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val lines = ["result = result + text"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### finds multiple patterns across lines

- finds multiple patterns across lines
- Verify: finds multiple patterns across lines
   - Expected: suggestions.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds multiple patterns across lines")
step("Verify: finds multiple patterns across lines")
val plugin = optimizer_plugin_source(
    "multi_check", [], ApplyMode.Static, OptLevel.Speed,
    ["result = result +", ".len()"]
)
val lines = ["for x in items:", "result = result + text", "val n = items.len()"]
val suggestions = optimizer_plugin_analyze_source(plugin, lines)
expect(suggestions.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### combined registry queries

#### filters scope then apply mode

- filters scope then apply mode
- Verify: filters scope then apply mode
   - Expected: mir_plugins.len() equals `2`
   - Expected: static_mir.len() equals `1`
   - Expected: first.name equals `dce`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("filters scope then apply mode")
step("Verify: filters scope then apply mode")
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
expect(mir_plugins.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
val static_mir = optimizer_plugin_registry_by_apply_mode(
    OptimizerPluginRegistry(plugins: mir_plugins), ApplyMode.Static
)
expect(static_mir.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val first = static_mir[0]
expect(first.name).to_equal("dce")
```

</details>

#### budget filter works across scopes

- budget filter works across scopes
- Verify: budget filter works across scopes
   - Expected: budget.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("budget filter works across scopes")
step("Verify: budget filter works across scopes")
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
expect(budget.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### MIR routing adapter

#### nil-guard returns function unchanged for source plugin

- nil-guard returns function unchanged for source plugin
- Verify: nil-guard returns function unchanged for source plugin
   - Expected: result.name equals `nilguard_fn`
   - Expected: result.blocks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("nil-guard returns function unchanged for source plugin")
step("Verify: nil-guard returns function unchanged for source plugin")
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
val result_r = optimizer_plugin_run_on_function(src_plugin, func)
match result_r:
    case Ok(result):
        expect(result.name).to_equal("nilguard_fn")
        expect(result.blocks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
    case Err(msg):
        assert_true(false)
```

</details>

#### WriteCoalesce via plugin transforms GEP+Store (inst count 4 to 5)

- WriteCoalesce via plugin transforms GEP+Store (inst count 4 to 5)
- Verify: WriteCoalesce via plugin transforms GEP+Store (inst count 4 to 5)
   - Expected: before.inst_count equals `4`
   - Expected: after.inst_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("WriteCoalesce via plugin transforms GEP+Store (inst count 4 to 5)")
step("Verify: WriteCoalesce via plugin transforms GEP+Store (inst count 4 to 5)")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
var idx0: [MirOperand] = []
idx0 = idx0.push(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0))))
var idx1: [MirOperand] = []
idx1 = idx1.push(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1))))
var insts: [MirInst] = []
insts = insts.push(MirInst(kind: MirInstKind.GetElementPtr(LocalId(id: 10), MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))), idx0), span: nil))
insts = insts.push(MirInst(kind: MirInstKind.Store(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 10))), MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(42)))), span: nil))
insts = insts.push(MirInst(kind: MirInstKind.GetElementPtr(LocalId(id: 11), MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))), idx1), span: nil))
insts = insts.push(MirInst(kind: MirInstKind.Store(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 11))), MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(99)))), span: nil))
val entry = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: insts, terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
locals = locals.push(MirLocal(id: LocalId(id: 1), type_: ty, kind: LocalKind.Temp, name: nil))
locals = locals.push(MirLocal(id: LocalId(id: 10), type_: ty, kind: LocalKind.Temp, name: nil))
locals = locals.push(MirLocal(id: LocalId(id: 11), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(
    symbol: SymbolId.new(0), name: "wc_fn", signature: sig,
    locals: locals, blocks: [entry], entry_block: BlockId.new(0),
    span: nil, generic_params: [], is_generic_template: false,
    specialization_of: nil, type_bindings: {}
)
var functions: Dict<SymbolId, MirFunction> = {}
functions[SymbolId.new(0)] = func
val module = MirModule(
    name: "wc_module", functions: functions,
    statics: {}, constants: {}, types: {}
)
val before = mir_inst_counter_count_module(module)
expect(before.inst_count).to_equal(4)  # oracle: 4 — named expected value from the requirement
val wc_plugin = optimizer_plugin_mir(
    "write_coalesce", [],
    PassKind.WriteCoalesce, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val result_r = optimizer_plugin_run_on_module(wc_plugin, module)
match result_r:
    case Ok(result):
        val after = mir_inst_counter_count_module(result)
        expect(after.inst_count).to_equal(5)  # oracle: 5 — named expected value from the requirement
    case Err(msg):
        assert_true(false)
```

</details>

#### source plugin nil-guard does NOT transform same GEP+Store module

- source plugin nil-guard does NOT transform same GEP+Store module
- Verify: source plugin nil-guard does NOT transform same GEP+Store module
   - Expected: before.inst_count equals `4`
   - Expected: after.inst_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("source plugin nil-guard does NOT transform same GEP+Store module")
step("Verify: source plugin nil-guard does NOT transform same GEP+Store module")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
var idx0: [MirOperand] = []
idx0 = idx0.push(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0))))
var idx1: [MirOperand] = []
idx1 = idx1.push(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1))))
var insts: [MirInst] = []
insts = insts.push(MirInst(kind: MirInstKind.GetElementPtr(LocalId(id: 10), MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))), idx0), span: nil))
insts = insts.push(MirInst(kind: MirInstKind.Store(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 10))), MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(42)))), span: nil))
insts = insts.push(MirInst(kind: MirInstKind.GetElementPtr(LocalId(id: 11), MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))), idx1), span: nil))
insts = insts.push(MirInst(kind: MirInstKind.Store(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 11))), MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(99)))), span: nil))
val entry = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: insts, terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
locals = locals.push(MirLocal(id: LocalId(id: 1), type_: ty, kind: LocalKind.Temp, name: nil))
locals = locals.push(MirLocal(id: LocalId(id: 10), type_: ty, kind: LocalKind.Temp, name: nil))
locals = locals.push(MirLocal(id: LocalId(id: 11), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(
    symbol: SymbolId.new(0), name: "nilguard_gep_fn", signature: sig,
    locals: locals, blocks: [entry], entry_block: BlockId.new(0),
    span: nil, generic_params: [], is_generic_template: false,
    specialization_of: nil, type_bindings: {}
)
var functions: Dict<SymbolId, MirFunction> = {}
functions[SymbolId.new(0)] = func
val module = MirModule(
    name: "nilguard_gep_module", functions: functions,
    statics: {}, constants: {}, types: {}
)
val before = mir_inst_counter_count_module(module)
expect(before.inst_count).to_equal(4)  # oracle: 4 — named expected value from the requirement
val src_plugin = optimizer_plugin_source(
    "string_concat", [], ApplyMode.Static, OptLevel.Speed, ["concat"]
)
val result_r = optimizer_plugin_run_on_module(src_plugin, module)
match result_r:
    case Ok(result):
        val after = mir_inst_counter_count_module(result)
        expect(after.inst_count).to_equal(4)  # oracle: 4 — named expected value from the requirement
    case Err(msg):
        assert_true(false)
```

</details>

### function-scope pass dispatch

#### DCE pass returns function unchanged

- DCE pass returns function unchanged
- Verify: DCE pass returns function unchanged
   - Expected: result.name equals `dce_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("DCE pass returns function unchanged")
step("Verify: DCE pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "dce_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.DeadCodeElimination, func)
expect(result.name).to_equal("dce_probe")
```

</details>

#### ConstantFolding pass returns function unchanged

- ConstantFolding pass returns function unchanged
- Verify: ConstantFolding pass returns function unchanged
   - Expected: result.name equals `cf_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ConstantFolding pass returns function unchanged")
step("Verify: ConstantFolding pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "cf_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.ConstantFolding, func)
expect(result.name).to_equal("cf_probe")
```

</details>

#### CopyPropagation pass returns function unchanged

- CopyPropagation pass returns function unchanged
- Verify: CopyPropagation pass returns function unchanged
   - Expected: result.name equals `cp_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CopyPropagation pass returns function unchanged")
step("Verify: CopyPropagation pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "cp_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.CopyPropagation, func)
expect(result.name).to_equal("cp_probe")
```

</details>

#### CSE pass returns function unchanged

- CSE pass returns function unchanged
- Verify: CSE pass returns function unchanged
   - Expected: result.name equals `cse_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CSE pass returns function unchanged")
step("Verify: CSE pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "cse_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.CommonSubexprElim, func)
expect(result.name).to_equal("cse_probe")
```

</details>

#### InlineSmallFunctions pass returns function unchanged

- InlineSmallFunctions pass returns function unchanged
- Verify: InlineSmallFunctions pass returns function unchanged
   - Expected: result.name equals `isf_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("InlineSmallFunctions pass returns function unchanged")
step("Verify: InlineSmallFunctions pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "isf_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.InlineSmallFunctions, func)
expect(result.name).to_equal("isf_probe")
```

</details>

<details>
<summary>Advanced: LoopInvariantMotion pass returns function unchanged</summary>

#### LoopInvariantMotion pass returns function unchanged

- LoopInvariantMotion pass returns function unchanged
- Verify: LoopInvariantMotion pass returns function unchanged
   - Expected: result.name equals `licm_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LoopInvariantMotion pass returns function unchanged")
step("Verify: LoopInvariantMotion pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "licm_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.LoopInvariantMotion, func)
expect(result.name).to_equal("licm_probe")
```

</details>


</details>

#### BoundsCheckElimination pass returns function unchanged

- BoundsCheckElimination pass returns function unchanged
- Verify: BoundsCheckElimination pass returns function unchanged
   - Expected: result.name equals `bce_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BoundsCheckElimination pass returns function unchanged")
step("Verify: BoundsCheckElimination pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "bce_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.BoundsCheckElimination, func)
expect(result.name).to_equal("bce_probe")
```

</details>

#### StrengthReduction pass returns function unchanged

- StrengthReduction pass returns function unchanged
- Verify: StrengthReduction pass returns function unchanged
   - Expected: result.name equals `sr_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("StrengthReduction pass returns function unchanged")
step("Verify: StrengthReduction pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "sr_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.StrengthReduction, func)
expect(result.name).to_equal("sr_probe")
```

</details>

#### TailCallOptimization pass returns function unchanged

- TailCallOptimization pass returns function unchanged
- Verify: TailCallOptimization pass returns function unchanged
   - Expected: result.name equals `tco_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TailCallOptimization pass returns function unchanged")
step("Verify: TailCallOptimization pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "tco_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.TailCallOptimization, func)
expect(result.name).to_equal("tco_probe")
```

</details>

#### GlobalValueNumbering pass returns function unchanged

- GlobalValueNumbering pass returns function unchanged
- Verify: GlobalValueNumbering pass returns function unchanged
   - Expected: result.name equals `gvn_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("GlobalValueNumbering pass returns function unchanged")
step("Verify: GlobalValueNumbering pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "gvn_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.GlobalValueNumbering, func)
expect(result.name).to_equal("gvn_probe")
```

</details>

#### TypedByteCanon pass returns function unchanged

- TypedByteCanon pass returns function unchanged
- Verify: TypedByteCanon pass returns function unchanged
   - Expected: result.name equals `tbc_probe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("TypedByteCanon pass returns function unchanged")
step("Verify: TypedByteCanon pass returns function unchanged")
val ty = MirType(kind: MirTypeKind.I64)
val sig = MirSignature(params: [], return_type: ty, is_variadic: false)
val inst = MirInst(kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(1), ty), span: nil)
val blk = MirBlock(id: BlockId(id: 0), label: Some("bb0"), instructions: [inst], terminator: MirTerminator.Ret(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))))))
var locals: [MirLocal] = []
locals = locals.push(MirLocal(id: LocalId(id: 0), type_: ty, kind: LocalKind.Temp, name: nil))
val func = MirFunction(symbol: SymbolId.new(0), name: "tbc_probe", signature: sig, locals: locals, blocks: [blk], entry_block: BlockId.new(0), span: nil, generic_params: [], is_generic_template: false, specialization_of: nil, type_bindings: {})
val result = run_typed_pass_on_function(PassKind.TypedByteCanon, func)
expect(result.name).to_equal("tbc_probe")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-MIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9736d3fe07e61772707d19939a0430b248ad551fdb607321d7506fac96cd94b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9736d3fe07e61772707d19939a0430b248ad551fdb607321d7506fac96cd94b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9736d3fe07e61772707d19939a0430b248ad551fdb607321d7506fac96cd94b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/optimizer_plugin_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/optimizer_plugin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/optimizer_plugin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/optimizer_plugin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/optimizer_plugin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/optimizer_plugin_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names Mir scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/optimizer_plugin_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names Source scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/optimizer_plugin_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names Both scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
