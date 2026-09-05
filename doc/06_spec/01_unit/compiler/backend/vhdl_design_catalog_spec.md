# Contract spec: test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl` and a green Results line.

## Scenarios

### VHDL design-wide catalog

#### recovers hardware metadata from the driver source sidecar

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recovers hardware metadata from the driver source sidecar
   - Expected: result.is_ok() is true
   - Expected: catalog.design.functions[symbol].has_vhdl_metadata is true
   - Expected: recovered.is_hardware is true
   - Expected: recovered.generics.len() equals `1`
   - Expected: recovered.generics[0].name equals `WIDTH`
   - Expected: recovered.generics[0].type_text equals `natural`
   - Expected: recovered.generics[0].default_text equals `32`
   - Expected: recovered.has_clocked is true
   - Expected: recovered.clocked.clock_signal equals `core_clk`
   - Expected: recovered.clocked.reset_signal equals `core_reset_n`
   - Expected: recovered.clocked.has_reset is true
   - Expected: recovered.clocked.reset_polarity equals `VhdlResetPolarity.ActiveLow`
   - Expected: recovered.clocked.reset_synchrony equals `VhdlResetSynchrony.Async`
   - Expected: recovered.clocked.domain equals `core`
   - Expected: recovered.return_fields.len() equals `2`
   - Expected: recovered.return_fields[0].label equals `ready`
   - Expected: recovered.return_fields[1].type_text equals `i32`
   - Expected: recovered.flatten_struct_output is true
   - Expected: catalog.hardware_entity_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("recovers hardware metadata from the driver source sidecar")
var mir = catalog_module_b("stage4_metadata_entry", false)
mir.name = "lib.stage4_metadata"
var modules: Dict<text, MirModule> = {}
modules[mir.name] = mir
val rows = [VhdlHardwareMetadataFlatRow(
    module_name: "std.stage4_metadata",
    function_name: "stage4_metadata_entry",
    generic_names: ["WIDTH"],
    generic_type_texts: ["natural"],
    generic_default_texts: ["32"],
    has_clocked: 1,
    clock_signal: "core_clk",
    reset_signal: "core_reset_n",
    has_reset: 1,
    reset_polarity: 0,
    reset_synchrony: 0,
    domain: "core",
    clocked_is_valid: 1,
    clocked_validation_errors: [],
    return_field_labels: ["ready", "result"],
    return_field_type_texts: ["bool", "i32"],
    flatten_struct_output: 1
)]
val result = vhdl_build_design_catalog_with_metadata(modules, {}, rows,
    [mir.name], "stage4_metadata_contract")
expect(result.is_ok()).to_equal(true)
val catalog = result.unwrap()
val symbol = SymbolId(id: catalog_function_symbol(catalog.design,
    "stage4_metadata_entry"))
expect(catalog.design.functions[symbol].has_vhdl_metadata).to_equal(true)
val recovered = catalog.design.functions[symbol].vhdl_metadata
expect(recovered.is_hardware).to_equal(true)
expect(recovered.generics.len()).to_equal(1)
expect(recovered.generics[0].name).to_equal("WIDTH")
expect(recovered.generics[0].type_text).to_equal("natural")
expect(recovered.generics[0].default_text).to_equal("32")
expect(recovered.has_clocked).to_equal(true)
expect(recovered.clocked.clock_signal).to_equal("core_clk")
expect(recovered.clocked.reset_signal).to_equal("core_reset_n")
expect(recovered.clocked.has_reset).to_equal(true)
expect(recovered.clocked.reset_polarity).to_equal(VhdlResetPolarity.ActiveLow)
expect(recovered.clocked.reset_synchrony).to_equal(VhdlResetSynchrony.Async)
expect(recovered.clocked.domain).to_equal("core")
expect(recovered.return_fields.len()).to_equal(2)
expect(recovered.return_fields[0].label).to_equal("ready")
expect(recovered.return_fields[1].type_text).to_equal("i32")
expect(recovered.flatten_struct_output).to_equal(true)
expect(catalog.hardware_entity_count).to_equal(1)
```

</details>

#### fails closed when no sidecar function name matches

- fails closed when no sidecar function name matches
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed when no sidecar function name matches")
val mir = catalog_module_b("stage4_metadata_entry", false)
var modules: Dict<text, MirModule> = {}
modules[mir.name] = mir
val rows = [catalog_flat_row("other.module", "other_entry")]
val result = vhdl_build_design_catalog_with_metadata(modules, {}, rows,
    [mir.name], "stage4_metadata_mismatch_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("found no @hardware entry")
```

</details>

#### does not classify an unrelated same-named sidecar function

- does not classify an unrelated same-named sidecar function
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not classify an unrelated same-named sidecar function")
val mir = catalog_module_b("stage4_metadata_entry", false)
var modules: Dict<text, MirModule> = {}
modules[mir.name] = mir
val rows = [catalog_flat_row("std.unrelated", "stage4_metadata_entry")]
val result = vhdl_build_design_catalog_with_metadata(modules, {}, rows,
    [mir.name], "stage4_metadata_unrelated_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("found no @hardware entry")
```

</details>

#### rejects ambiguous normalized metadata aliases

- rejects ambiguous normalized metadata aliases
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects ambiguous normalized metadata aliases")
var mir = catalog_module_b("stage4_metadata_entry", false)
mir.name = "stage4_metadata"
var modules: Dict<text, MirModule> = {}
modules[mir.name] = mir
val rows = [
    catalog_flat_row("std.stage4_metadata", "stage4_metadata_entry"),
    catalog_flat_row("lib.stage4_metadata", "stage4_metadata_entry")
]
val result = vhdl_build_design_catalog_with_metadata(modules, {}, rows,
    [mir.name], "stage4_metadata_ambiguous_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("is ambiguous")
```

</details>

#### rejects an exact metadata row plus its normalized alias

- rejects an exact metadata row plus its normalized alias
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an exact metadata row plus its normalized alias")
var mir = catalog_module_b("stage4_metadata_entry", false)
mir.name = "lib.stage4_metadata"
var modules: Dict<text, MirModule> = {}
modules[mir.name] = mir
val rows = [
    catalog_flat_row("lib.stage4_metadata", "stage4_metadata_entry"),
    catalog_flat_row("std.stage4_metadata", "stage4_metadata_entry")
]
val result = vhdl_build_design_catalog_with_metadata(modules, {}, rows,
    [mir.name], "stage4_metadata_exact_alias_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("is ambiguous")
```

</details>

#### rejects a generic hardware entry before VHDL emission

- rejects a generic hardware entry before VHDL emission
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a generic hardware entry before VHDL emission")
var mir = catalog_module_b("generic_entry", false)
val symbol = SymbolId(id: catalog_function_symbol(mir, "generic_entry"))
var func = mir.functions[symbol]
func.generic_params = ["T"]
func.is_generic_template = true
mir.functions[symbol] = func
var modules: Dict<text, MirModule> = {}
modules[mir.name] = mir
val rows = [catalog_flat_row(mir.name, "generic_entry")]
val result = vhdl_build_design_catalog_with_metadata(modules, {}, rows,
    [mir.name], "generic_hardware_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("is generic")
```

</details>

#### rejects flat metadata with mismatched parallel arrays

- rejects flat metadata with mismatched parallel arrays
   - Expected: result.is_err() is true
   - Expected: tag_result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects flat metadata with mismatched parallel arrays")
val mir = catalog_module_b("invalid_metadata_entry", false)
var modules: Dict<text, MirModule> = {}
modules[mir.name] = mir
var row = catalog_flat_row(mir.name, "invalid_metadata_entry")
row.generic_names = ["WIDTH"]
row.generic_default_texts = ["32"]
row.generic_type_texts = []
val result = vhdl_build_design_catalog_with_metadata(modules, {}, [row],
    [mir.name], "invalid_flat_metadata_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("invalid flat fields")
var invalid_tag = catalog_flat_row(mir.name, "invalid_metadata_entry")
invalid_tag.reset_synchrony = 3
val tag_result = vhdl_build_design_catalog_with_metadata(modules, {},
    [invalid_tag], [mir.name], "invalid_flat_tag_contract")
expect(tag_result.is_err()).to_equal(true)
expect(tag_result.unwrap_err()).to_contain("invalid flat fields")
```

</details>

#### rebases module-local symbols and orders record dependencies

- rebases module-local symbols and orders record dependencies
   - Expected: result.is_ok() is true
   - Expected: catalog.design.functions.len() equals `3`
   - Expected: catalog.design.types.len() equals `2`
   - Expected: catalog.type_order.len() equals `2`
   - Expected: catalog.design.types[catalog.type_order[0]].name equals `base_t`
   - Expected: catalog.design.types[catalog.type_order[1]].name equals `wrapper_t`
   - Expected: catalog.source_module_count equals `3`
   - Expected: catalog.hardware_entity_count equals `2`
   - Expected: top_source equals `entry`
   - Expected: leaf_source equals `a`
   - Expected: helper_source equals `b`
   - Expected: compiled.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rebases module-local symbols and orders record dependencies")
var modules: Dict<text, MirModule> = {}
modules["a"] = catalog_module_a()
modules["b"] = catalog_module_b("catalog_helper", false)
modules["entry"] = catalog_entry_module()
val result = vhdl_build_design_catalog(modules, "catalog_contract")
expect(result.is_ok()).to_equal(true)
val catalog = result.unwrap()
expect(catalog.design.functions.len()).to_equal(3)
expect(catalog.design.types.len()).to_equal(2)
expect(catalog.type_order.len()).to_equal(2)
expect(catalog.design.types[catalog.type_order[0]].name).to_equal("base_t")
expect(catalog.design.types[catalog.type_order[1]].name).to_equal("wrapper_t")
expect(catalog.source_module_count).to_equal(3)
expect(catalog.hardware_entity_count).to_equal(2)
var top_source = ""
var leaf_source = ""
var helper_source = ""
for source in catalog.function_sources:
    if source.name == "catalog_top":
        top_source = source.source_module
    elif source.name == "catalog_leaf":
        leaf_source = source.source_module
    elif source.name == "catalog_helper":
        helper_source = source.source_module
expect(top_source).to_equal("entry")
expect(leaf_source).to_equal("a")
expect(helper_source).to_equal("b")
val compiled = VhdlBackend.create(CodegenTarget.Riscv32,
    compileoptions_default_options()).compile(catalog.design)
expect(compiled.is_ok()).to_equal(true)
val output = compiled.unwrap()
val package = output.package_vhdl.unwrap()
expect(package).to_contain("function catalog_helper")
expect(package.index_of("type base_t is")).to_be_less_than(
    package.index_of("type wrapper_t is"))
expect(output.vhdl).to_contain("entity catalog_leaf is")
expect(output.vhdl).to_contain("entity catalog_top is")
expect(output.vhdl.index_of("entity catalog_leaf is")).to_be_less_than(
    output.vhdl.index_of("entity catalog_top is"))
```

</details>

#### rebases colliding module-local functions with flat metadata and source ownership

- rebases colliding module-local functions with flat metadata and source ownership
   - Expected: result.is_ok() is true
   - Expected: helper_symbol == top_symbol is false
   - Expected: catalog.hardware_entity_count equals `1`
   - Expected: rebased_top.has_vhdl_metadata is true
   - Expected: rebased_top.vhdl_metadata.is_hardware is true
   - Expected: helper_source equals `helper`
   - Expected: top_source equals `entry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rebases colliding module-local functions with flat metadata and source ownership")
val helper = catalog_module_b("catalog_rebase_helper", false)
var entry = catalog_call_entry_module("helper::catalog_rebase_helper")
val entry_symbol = SymbolId(id: catalog_function_symbol(entry, "catalog_call_top"))
var entry_function = entry.functions[entry_symbol]
entry_function.has_vhdl_metadata = false
entry_function.vhdl_metadata = vhdl_hardware_metadata_default()
entry.functions[entry_symbol] = entry_function
expect(catalog_function_symbol(helper, "catalog_rebase_helper")).to_equal(
    catalog_function_symbol(entry, "catalog_call_top"))
var modules: Dict<text, MirModule> = {}
modules["helper"] = helper
modules["entry"] = entry
val result = vhdl_build_design_catalog_with_metadata(modules, {},
    [catalog_flat_row("entry", "catalog_call_top")], ["entry"],
    "catalog_rebase_ownership_contract")
expect(result.is_ok()).to_equal(true)
val catalog = result.unwrap()
val helper_symbol = catalog_function_symbol(catalog.design,
    "catalog_rebase_helper")
val top_symbol = catalog_function_symbol(catalog.design, "catalog_call_top")
expect(helper_symbol).to_be_greater_than(0)
expect(top_symbol).to_be_greater_than(0)
expect(helper_symbol == top_symbol).to_equal(false)
expect(catalog.hardware_entity_count).to_equal(1)
val rebased_top = catalog.design.functions[SymbolId(id: top_symbol)]
expect(rebased_top.has_vhdl_metadata).to_equal(true)
expect(rebased_top.vhdl_metadata.is_hardware).to_equal(true)
var helper_source = ""
var top_source = ""
for source in catalog.function_sources:
    if source.name == "catalog_rebase_helper":
        helper_source = source.source_module
    elif source.name == "catalog_call_top":
        top_source = source.source_module
expect(helper_source).to_equal("helper")
expect(top_source).to_equal("entry")
```

</details>

#### uses HIR provenance for imported types and globals and rebases nested static initializers

- uses HIR provenance for imported types and globals and rebases nested static initializers
   - Expected: result.is_ok() is true
   - Expected: catalog.design.functions.len() equals `1`
   - Expected: catalog.design.types.len() equals `1`
   - Expected: catalog.design.statics.len() equals `1`
   - Expected: catalog.design.constants.len() equals `1`
   - Expected: catalog.root_modules.len() equals `1`
   - Expected: catalog.root_modules[0] equals `entry`
   - Expected: catalog.reachable_source_modules.len() equals `2`
   - Expected: catalog.reachable_source_modules[0] equals `entry`
   - Expected: catalog.reachable_source_modules[1] equals `owner`
   - Expected: catalog.source_rows.len() equals `2`
   - Expected: catalog.function_sources.len() equals `1`
   - Expected: catalog.helper_function_count equals `0`
   - Expected: catalog.type_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses HIR provenance for imported types and globals and rebases nested static initializers")
var modules: Dict<text, MirModule> = {}
modules["owner"] = catalog_owner_module()
modules["entry"] = catalog_import_entry_module(0)
var hir_modules: Dict<text, HirModule> = {}
hir_modules["owner"] = catalog_hir_module("owner")
hir_modules["entry"] = catalog_hir_module("entry")
val result = vhdl_build_design_catalog_with_hir(modules, hir_modules,
    ["entry"], "catalog_import_contract")
expect(result.is_ok()).to_equal(true)
val catalog = result.unwrap()
expect(catalog.design.functions.len()).to_equal(1)
expect(catalog.design.types.len()).to_equal(1)
expect(catalog.design.statics.len()).to_equal(1)
expect(catalog.design.constants.len()).to_equal(1)
expect(catalog.root_modules.len()).to_equal(1)
expect(catalog.root_modules[0]).to_equal("entry")
expect(catalog.reachable_source_modules.len()).to_equal(2)
expect(catalog.reachable_source_modules[0]).to_equal("entry")
expect(catalog.reachable_source_modules[1]).to_equal("owner")
expect(catalog.source_rows.len()).to_equal(2)
expect(catalog.function_sources.len()).to_equal(1)
expect(catalog.helper_function_count).to_equal(0)
expect(catalog.type_count).to_equal(1)
val static_symbol = catalog.design.statics.keys()[0]
expect(static_symbol.id).to_be_greater_than(0)
val retained = catalog.design.statics[static_symbol]
expect(retained.init.unwrap().symbol.id).to_be_greater_than(0)
val root_symbol = catalog.design.functions.keys()[0]
val root_function = catalog.design.functions[root_symbol]
match root_function.locals[1].type_.kind:
    case MirTypeKind.Struct(symbol): expect(symbol.id).to_equal(
        catalog.design.types.keys()[0].id)
    case _: expect(false).to_equal(true)
val root_inst = root_function.blocks[0].instructions[0]
match root_inst.kind:
    case LoadGlobal(_, symbol): expect(symbol.id).to_equal(static_symbol.id)
    case _: expect(false).to_equal(true)
```

</details>

#### fails at the catalog boundary for an unmapped imported global

- fails at the catalog boundary for an unmapped imported global
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails at the catalog boundary for an unmapped imported global")
var modules: Dict<text, MirModule> = {}
modules["owner"] = catalog_owner_module()
modules["entry"] = catalog_import_entry_module(99)
var hir_modules: Dict<text, HirModule> = {}
hir_modules["owner"] = catalog_hir_module("owner")
hir_modules["entry"] = catalog_hir_module("entry")
val result = vhdl_build_design_catalog_with_hir(modules, hir_modules,
    ["entry"], "catalog_import_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("unmapped global/static symbol")
```

</details>

#### retains hardware entities referenced by explicit port maps

- retains hardware entities referenced by explicit port maps
   - Expected: result.is_ok() is true
   - Expected: catalog.design.functions.len() equals `2`
   - Expected: catalog.hardware_entity_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains hardware entities referenced by explicit port maps")
var modules: Dict<text, MirModule> = {}
modules["leaf"] = catalog_module_b("catalog_leaf", true)
modules["entry"] = catalog_portmap_entry_module("leaf::catalog_leaf")
val result = vhdl_build_design_catalog_with_hir(modules, {}, ["entry"],
    "catalog_portmap_contract")
expect(result.is_ok()).to_equal(true)
val catalog = result.unwrap()
expect(catalog.design.functions.len()).to_equal(2)
expect(catalog.hardware_entity_count).to_equal(2)
expect(catalog_function_symbol(catalog.design, "catalog_leaf")).to_be_greater_than(0)
val top_symbol = SymbolId(id: catalog_function_symbol(catalog.design,
    "catalog_portmap_top"))
match catalog.design.functions[top_symbol].blocks[0].instructions[0].kind:
    case VhdlPortMap(entity, _, _): expect(entity).to_equal("catalog_leaf")
    case _: expect(false).to_equal(true)
```

</details>

#### fails closed when an explicit port-map entity does not resolve

- fails closed when an explicit port-map entity does not resolve
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed when an explicit port-map entity does not resolve")
var modules: Dict<text, MirModule> = {}
modules["entry"] = catalog_portmap_entry_module("catalog_leaf")
val result = vhdl_build_design_catalog_with_hir(modules, {}, ["entry"],
    "catalog_missing_portmap_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("Unresolved VHDL port-map entity")
```

</details>

#### rejects ambiguous bare port-map entity names across modules

- rejects ambiguous bare port-map entity names across modules
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects ambiguous bare port-map entity names across modules")
var modules: Dict<text, MirModule> = {}
modules["a"] = catalog_module_b("shared_entity", true)
modules["b"] = catalog_module_b("shared_entity", true)
modules["entry"] = catalog_portmap_entry_module("shared_entity")
val result = vhdl_build_design_catalog_with_hir(modules, {}, ["entry"],
    "catalog_ambiguous_portmap_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("Ambiguous VHDL port-map entity")
```

</details>

#### rejects ambiguous bare call names across modules

- rejects ambiguous bare call names across modules
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects ambiguous bare call names across modules")
var modules: Dict<text, MirModule> = {}
modules["a"] = catalog_module_b("shared_helper", false)
modules["b"] = catalog_module_b("shared_helper", false)
modules["entry"] = catalog_call_entry_module("shared_helper")
val result = vhdl_build_design_catalog_with_hir(modules, {}, ["entry"],
    "catalog_ambiguous_call_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("Ambiguous VHDL design call target")
```

</details>

#### resolves a module-qualified call identity and prunes its bare-name sibling

- resolves a module-qualified call identity and prunes its bare-name sibling
   - Expected: result.is_ok() is true
   - Expected: catalog.design.functions.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves a module-qualified call identity and prunes its bare-name sibling")
var modules: Dict<text, MirModule> = {}
modules["a"] = catalog_module_b("shared_helper", false)
modules["b"] = catalog_module_b("shared_helper", false)
modules["entry"] = catalog_call_entry_module("a::shared_helper")
val result = vhdl_build_design_catalog_with_hir(modules, {}, ["entry"],
    "catalog_qualified_call_contract")
expect(result.is_ok()).to_equal(true)
val catalog = result.unwrap()
expect(catalog.design.functions.len()).to_equal(2)
expect(catalog_function_symbol(catalog.design, "shared_helper")).to_be_greater_than(0)
val top_symbol = SymbolId(id: catalog_function_symbol(catalog.design,
    "catalog_call_top"))
match catalog.design.functions[top_symbol].blocks[0].instructions[0].kind:
    case Call(_, operand, _):
        match operand.kind:
            case Const(Str(name), _): expect(name).to_equal("shared_helper")
            case _: expect(false).to_equal(true)
    case _: expect(false).to_equal(true)
```

</details>

#### fails at the catalog boundary for instruction-embedded unmapped types

- fails at the catalog boundary for instruction-embedded unmapped types
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails at the catalog boundary for instruction-embedded unmapped types")
var modules: Dict<text, MirModule> = {}
modules["entry"] = catalog_unmapped_aggregate_entry_module()
val result = vhdl_build_design_catalog_with_hir(modules, {}, ["entry"],
    "catalog_unmapped_type_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("unmapped type symbol")
```

</details>

#### is deterministic when source modules are inserted in reverse order

- is deterministic when source modules are inserted in reverse order
   - Expected: first.root_modules.len() equals `second.root_modules.len()`
   - Expected: first.root_modules[0] equals `second.root_modules[0]`
   - Expected: first_vhdl.package_vhdl.unwrap() equals `second_vhdl.package_vhdl.unwrap()`
   - Expected: first_vhdl.vhdl equals `second_vhdl.vhdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is deterministic when source modules are inserted in reverse order")
var forward: Dict<text, MirModule> = {}
forward["a"] = catalog_module_a()
forward["b"] = catalog_module_b("catalog_helper", false)
forward["entry"] = catalog_entry_module()
var reverse: Dict<text, MirModule> = {}
reverse["entry"] = catalog_entry_module()
reverse["b"] = catalog_module_b("catalog_helper", false)
reverse["a"] = catalog_module_a()
val first = vhdl_build_design_catalog(forward, "catalog_contract").unwrap()
val second = vhdl_build_design_catalog(reverse, "catalog_contract").unwrap()
expect(first.root_modules.len()).to_equal(second.root_modules.len())
expect(first.root_modules[0]).to_equal(second.root_modules[0])
expect(first.reachable_source_modules.len()).to_equal(
    second.reachable_source_modules.len())
expect(first.reachable_source_modules[0]).to_equal(
    second.reachable_source_modules[0])
expect(first.source_rows[0].module_name).to_equal(
    second.source_rows[0].module_name)
expect(first.source_rows[0].function_count).to_equal(
    second.source_rows[0].function_count)
expect(catalog_function_symbol(first.design, "catalog_top")).to_equal(
    catalog_function_symbol(second.design, "catalog_top"))
expect(catalog_function_symbol(first.design, "catalog_helper")).to_equal(
    catalog_function_symbol(second.design, "catalog_helper"))
val first_vhdl = VhdlBackend.create(CodegenTarget.Riscv32,
    compileoptions_default_options()).compile(first.design).unwrap()
val second_vhdl = VhdlBackend.create(CodegenTarget.Riscv32,
    compileoptions_default_options()).compile(second.design).unwrap()
expect(first_vhdl.package_vhdl.unwrap()).to_equal(second_vhdl.package_vhdl.unwrap())
expect(first_vhdl.vhdl).to_equal(second_vhdl.vhdl)
```

</details>

#### fails closed on design-wide emitted-name conflicts

- fails closed on design-wide emitted-name conflicts
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed on design-wide emitted-name conflicts")
var modules: Dict<text, MirModule> = {}
modules["a"] = catalog_module_b("duplicate_name", true)
modules["b"] = catalog_module_b("DUPLICATE_NAME", true)
val result = vhdl_build_design_catalog(modules, "catalog_contract")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("Conflicting VHDL function/entity name")
```

</details>

#### fails closed on cyclic reachable record dependencies

- fails closed on cyclic reachable record dependencies
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed on cyclic reachable record dependencies")
val left = MirTypeDef(symbol: SymbolId(id: 1), name: "left_t",
    kind: MirTypeDefKind.Struct([MirFieldDef(name: "right",
        type_: MirType(kind: MirTypeKind.Struct(SymbolId(id: 2))),
        offset: 0, has_bits_attr: false, bits_width: 0)]),
    is_export_c: false, export_name: "")
val right = MirTypeDef(symbol: SymbolId(id: 2), name: "right_t",
    kind: MirTypeDefKind.Struct([MirFieldDef(name: "left",
        type_: MirType(kind: MirTypeKind.Struct(SymbolId(id: 1))),
        offset: 0, has_bits_attr: false, bits_width: 0)]),
    is_export_c: false, export_name: "")
var types: Dict<SymbolId, MirTypeDef> = {}
types[left.symbol] = left
types[right.symbol] = right
val result = vhdl_catalog_type_order(types)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("cyclic record/enum type dependency")
```

</details>

#### selects the VHDL root only from explicit compile inputs, never native-build env

- selects the VHDL root only from explicit compile inputs, never native-build env


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects the VHDL root only from explicit compile inputs, never native-build env")
val source = rt_file_read_text(
    "src/compiler/80.driver/driver_aot_vhdl_output.spl") ?? ""
expect(source).to_not_contain("rt_env_get(\"SIMPLE_NATIVE_BUILD_ENTRY\")")        expect(source).to_contain("driver_vhdl_entry_module(ctx)")
expect(source).to_contain("ctx.options.bootstrap_input_0")
expect(source).to_contain("VHDL compilation requires one explicit entry file in compile options")
expect(source).to_contain("VHDL compilation entry is ambiguous")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b355026644211be4c351483f84f4770d34011d00225266d648e7c82f28f4e71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b355026644211be4c351483f84f4770d34011d00225266d648e7c82f28f4e71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b355026644211be4c351483f84f4770d34011d00225266d648e7c82f28f4e71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vhdl_design_catalog_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl:240:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recovers hardware metadata from the driver source sidecar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl:292:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when no sidecar function name matches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl:304:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not classify an unrelated same-named sidecar function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
