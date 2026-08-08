# Resolve Import Symbols Unit Spec

> Verifies that explicit, glob, and aliased imports register symbols from the

<!-- sdn-diagram:id=resolve_import_symbols_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resolve_import_symbols_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resolve_import_symbols_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resolve_import_symbols_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resolve Import Symbols Unit Spec

Verifies that explicit, glob, and aliased imports register symbols from the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/resolve_import_symbols_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that explicit, glob, and aliased imports register symbols from the
requested source module even when another loaded module exports the same name.

## Scenarios

### resolve_import_symbols 2-pass import resolver
_The import pre-pass must preserve module identity before HIR lowering resolves symbol uses._

#### named import from module A wins over same-named symbol from module B

- var lowering = HirLowering with filename
   - Expected: resolved_id.? is true
   - Expected: sym.? is true
   - Expected: defining_mod.? is true
   - Expected: defining_mod.unwrap() equals `path_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = make_logger()

# Module A: CompileOptions has only_in_a (unique sentinel field)
val src_a = "struct CompileOptions:\n    input_files: [text]\n    only_in_a: i64"
val path_a = "a"
val module_a = parse_full_frontend(src_a, path_a, path_a, log)

# Module B: CompileOptions has only_in_b (unique sentinel field)
val src_b = "struct CompileOptions:\n    mode: text\n    only_in_b: i64"
val path_b = "b"
val module_b = parse_full_frontend(src_b, path_b, path_b, log)

# Consumer: explicitly imports CompileOptions from module A
val open = "{"
val close = "}"
val src_consumer = "use a." + open + "CompileOptions" + close
val path_consumer = "consumer"
val module_consumer = parse_full_frontend(src_consumer, path_consumer, path_consumer, log)

# Wire up modules map — both modules available to resolve_import_symbols
var modules_map: Dict<text, any> = {}
modules_map[path_a] = module_a
modules_map[path_b] = module_b

# Lower the consumer with modules_by_name set
# resolve_import_symbols must pre-register A's CompileOptions first
var lowering = HirLowering.with_filename(path_consumer)
lowering.modules_by_name = modules_map
val hir_consumer = lowering.lower_module(module_consumer)

# CompileOptions must resolve to the entry registered from module A
val resolved_id = hir_consumer.symbols.lookup("CompileOptions")
expect(resolved_id.?).to_equal(true)

val sym = hir_consumer.symbols.get_symbol(resolved_id)
expect(sym.?).to_equal(true)

if val sym_value = sym:
    val defining_mod = sym_value.defining_module
    expect(defining_mod.?).to_equal(true)
    # Must resolve to module A (the explicit import target), not B
    expect(defining_mod.unwrap()).to_equal(path_a)
```

</details>

#### glob import pre-registers all type symbols from imported module

- var lowering2 = HirLowering with filename
   - Expected: foo_id.? is true
   - Expected: bar_id.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = make_logger()

# Library module with two types
val src_lib = "struct Foo:\n    x: i64\nstruct Bar:\n    y: text"
val path_lib = "mylib"
val module_lib = parse_full_frontend(src_lib, path_lib, path_lib, log)

# Consumer uses glob import
val src_consumer2 = "use mylib.*"
val path_consumer2 = "consumer2"
val module_consumer2 = parse_full_frontend(src_consumer2, path_consumer2, path_consumer2, log)

var modules_map2: Dict<text, any> = {}
modules_map2[path_lib] = module_lib

var lowering2 = HirLowering.with_filename(path_consumer2)
lowering2.modules_by_name = modules_map2
val hir2 = lowering2.lower_module(module_consumer2)

# Both Foo and Bar must be resolvable in the consumer's symbol table
val foo_id = hir2.symbols.lookup("Foo")
val bar_id = hir2.symbols.lookup("Bar")
expect(foo_id.?).to_equal(true)
expect(bar_id.?).to_equal(true)
```

</details>

#### aliased imports keep same-named structs from different modules distinct

- var lowering = HirLowering with filename
   - Expected: driver_id.? is true
   - Expected: backend_id.? is true
   - Expected: driver_value.defining_module.unwrap() equals `path_driver`
   - Expected: backend_value.defining_module.unwrap() equals `path_backend`
   - Expected: driver_symbol_id.id == backend_symbol_id.id is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = make_logger()

val src_driver = "struct CompileOptions:\n    input_files: [text]\n    low_memory: bool"
val path_driver = "driver_types"
val module_driver = parse_full_frontend(src_driver, path_driver, path_driver, log)

val src_backend = "struct CompileOptions:\n    target: text\n    verify_output: bool"
val path_backend = "backend_types"
val module_backend = parse_full_frontend(src_backend, path_backend, path_backend, log)

val open = "{"
val close = "}"
val src_consumer = "use driver_types." + open + "CompileOptions as DriverOptions" + close + "\n" +
    "use backend_types." + open + "CompileOptions as BackendOptions" + close
val path_consumer = "consumer_aliases"
val module_consumer = parse_full_frontend(src_consumer, path_consumer, path_consumer, log)

var modules_map: Dict<text, any> = {}
modules_map[path_driver] = module_driver
modules_map[path_backend] = module_backend

var lowering = HirLowering.with_filename(path_consumer)
lowering.modules_by_name = modules_map
val hir = lowering.lower_module(module_consumer)

val driver_id = hir.symbols.lookup("DriverOptions")
val backend_id = hir.symbols.lookup("BackendOptions")
expect(driver_id.?).to_equal(true)
expect(backend_id.?).to_equal(true)

val driver_sym = hir.symbols.get_symbol(driver_id)
val backend_sym = hir.symbols.get_symbol(backend_id)
if val driver_value = driver_sym:
    expect(driver_value.defining_module.unwrap()).to_equal(path_driver)
if val backend_value = backend_sym:
    expect(backend_value.defining_module.unwrap()).to_equal(path_backend)
if val driver_symbol_id = driver_id:
    if val backend_symbol_id = backend_id:
        expect(driver_symbol_id.id == backend_symbol_id.id).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
