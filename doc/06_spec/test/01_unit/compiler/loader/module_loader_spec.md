# Module Loader

> Verifies module loading, JIT symbol resolution, and cache cleanup behavior.

<!-- sdn-diagram:id=module_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader

Verifies module loading, JIT symbol resolution, and cache cleanup behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/module_loader_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies module loading, JIT symbol resolution, and cache cleanup behavior.

## Scenarios

### Module Loader
_Focused module loader behavior checks._

#### creates default configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ModuleLoaderConfig.default()
expect(config.enable_jit).to_equal(true)
expect(config.enable_cache).to_equal(true)
expect(config.max_cache_size).to_equal(100)
expect(config.hot_reload).to_equal(false)
```

</details>

#### loads an existing path and tracks it as loaded

- var loader = ModuleLoader with defaults
   - Expected: module.path equals `path`
   - Expected: "unexpected" equals `path`
   - Expected: loader.is_loaded(path) is true
   - Expected: loader.loaded_modules().len() equals `1`
   - Expected: loader.stats().module_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val result = loader.load(path)

match result:
    case LoadResult.Success(module):
        expect(module.path).to_equal(path)
    case _:
        expect("unexpected").to_equal(path)

expect(loader.is_loaded(path)).to_equal(true)
expect(loader.loaded_modules().len()).to_equal(1)
expect(loader.stats().module_count).to_equal(1)
```

</details>

#### loads a module with a symbol and resolves it from globals

- var loader = ModuleLoader with defaults
   - Expected: module.path equals `path`
   - Expected: "unexpected" equals `path`
- loader global symbols = {"module exported fn":
   - Expected: found.name equals `module_exported_fn`
   - Expected: found.address equals `4096`
   - Expected: found.size equals `16`
   - Expected: found.ty equals `SymbolType.Function`
   - Expected: found.is_jit is false
   - Expected: found.file_offset equals `8`
   - Expected: code.len() equals `0`
   - Expected: "missing" equals `module_exported_fn`
   - Expected: loader.stats().symbol_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val loaded = loader.load(path)

match loaded:
    case LoadResult.Success(module):
        expect(module.path).to_equal(path)
    case _:
        expect("unexpected").to_equal(path)

val symbol = LoadedSymbol(
    name: "module_exported_fn",
    address: 4096,
    size: 16,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 8
)
loader.global_symbols = {"module_exported_fn": (path, symbol)}

val resolved = moduleloader_resolve_symbol(loader, "module_exported_fn")
match resolved:
    case SymbolResult.Found(found, code):
        expect(found.name).to_equal("module_exported_fn")
        expect(found.address).to_equal(4096)
        expect(found.size).to_equal(16)
        expect(found.ty).to_equal(SymbolType.Function)
        expect(found.is_jit).to_equal(false)
        expect(found.file_offset).to_equal(8)
        expect(code.len()).to_equal(0)
    case _:
        expect("missing").to_equal("module_exported_fn")

expect(loader.stats().symbol_count).to_equal(1)
```

</details>

#### loads multiple existing paths and reports module count

- var loader = ModuleLoader with defaults
   - Expected: module.path equals `first_path`
   - Expected: "unexpected" equals `first_path`
   - Expected: module.path equals `second_path`
   - Expected: "unexpected" equals `second_path`
   - Expected: loader.is_loaded(first_path) is true
   - Expected: loader.is_loaded(second_path) is true
   - Expected: loader.loaded_modules().len() equals `2`
   - Expected: loader.stats().module_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val first_path = existing_module_path()
val second_path = second_module_path()
val first = loader.load(first_path)
val second = loader.load(second_path)

match first:
    case LoadResult.Success(module):
        expect(module.path).to_equal(first_path)
    case _:
        expect("unexpected").to_equal(first_path)

match second:
    case LoadResult.Success(module):
        expect(module.path).to_equal(second_path)
    case _:
        expect("unexpected").to_equal(second_path)

expect(loader.is_loaded(first_path)).to_equal(true)
expect(loader.is_loaded(second_path)).to_equal(true)
expect(loader.loaded_modules().len()).to_equal(2)
expect(loader.stats().module_count).to_equal(2)
```

</details>

#### loads modules and reports resolved symbol count

- var loader = ModuleLoader with defaults
-   = loader load
-   = loader load
- loader jit set metadata for test
- loader jit set metadata for test
   - Expected: symbol.name equals `vec_runtime_i64`
   - Expected: "missing" equals `vec_runtime_i64`
   - Expected: symbol.name equals `map_runtime_text_i64`
   - Expected: "missing" equals `map_runtime_text_i64`
   - Expected: loader.global_symbols.has("vec_runtime_i64") is true
   - Expected: loader.global_symbols.has("map_runtime_text_i64") is true
   - Expected: loader.stats().symbol_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val first_path = existing_module_path()
val second_path = second_module_path()
_ = loader.load(first_path)
_ = loader.load(second_path)
val first_entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "vec_runtime_i64"
)
val second_entry = PossibleInstantiation(
    template_name: "Map",
    type_args: "text_i64",
    mangled_name: "map_runtime_text_i64"
)
loader.jit.set_metadata_for_test(first_path, LoadedMetadata(possible: [first_entry], instantiations: []))
loader.jit.set_metadata_for_test(second_path, LoadedMetadata(possible: [second_entry], instantiations: []))

match loader.resolve_symbol("vec_runtime_i64"):
    case SymbolResult.JitCompiled(symbol, _):
        expect(symbol.name).to_equal("vec_runtime_i64")
    case _:
        expect("missing").to_equal("vec_runtime_i64")

match loader.resolve_symbol("map_runtime_text_i64"):
    case SymbolResult.JitCompiled(symbol, _):
        expect(symbol.name).to_equal("map_runtime_text_i64")
    case _:
        expect("missing").to_equal("map_runtime_text_i64")

expect(loader.global_symbols.has("vec_runtime_i64")).to_equal(true)
expect(loader.global_symbols.has("map_runtime_text_i64")).to_equal(true)
expect(loader.stats().symbol_count).to_equal(2)
```

</details>

#### returns an error when the module path does not exist

- var loader = ModuleLoader with defaults
   - Expected: "unexpected" equals `module not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val result = moduleloader_load(loader, "test/unit/compiler/loader/does_not_exist.spl")

match result:
    case LoadResult.Error(message):
        expect(message).to_contain("module not found")
    case _:
        expect("unexpected").to_equal("module not found")
```

</details>

#### resolves JIT-backed symbols through the public loader API

- var loader = ModuleLoader with defaults
- loader jit set metadata for test
   - Expected: symbol.name equals `vec_runtime_i64`
   - Expected: symbol.is_jit is true
   - Expected: "missing" equals `vec_runtime_i64`
   - Expected: loader.global_symbols.has("vec_runtime_i64") is true
   - Expected: symbol.name equals `vec_runtime_i64`
   - Expected: symbol.is_jit is true
   - Expected: code.len() equals `0`
   - Expected: "missing" equals `vec_runtime_i64`
   - Expected: loader.jit.stats().compile_count equals `1`
   - Expected: loader.jit.stats().cached_count equals `1`
   - Expected: loader.stats().symbol_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "vec_runtime_i64"
)
loader.jit.set_metadata_for_test(path, LoadedMetadata(possible: [entry], instantiations: []))

val result = loader.resolve_symbol("vec_runtime_i64")
match result:
    case SymbolResult.JitCompiled(symbol, code):
        expect(symbol.name).to_equal("vec_runtime_i64")
        expect(symbol.is_jit).to_equal(true)
        expect(code.len()).to_be_greater_than(0)
    case _:
        expect("missing").to_equal("vec_runtime_i64")

expect(loader.global_symbols.has("vec_runtime_i64")).to_equal(true)
val cached = loader.resolve_symbol("vec_runtime_i64")
match cached:
    case SymbolResult.Found(symbol, code):
        expect(symbol.name).to_equal("vec_runtime_i64")
        expect(symbol.is_jit).to_equal(true)
        expect(code.len()).to_equal(0)
    case _:
        expect("missing").to_equal("vec_runtime_i64")

expect(loader.jit.stats().compile_count).to_equal(1)
expect(loader.jit.stats().cached_count).to_equal(1)
expect(loader.stats().symbol_count).to_equal(1)
```

</details>

#### mangles explicit generic type arguments

- var loader = ModuleLoader with defaults
   - Expected: loader.config.enable_jit is true
   - Expected: name equals `Vec$Int_String`
   - Expected: "unexpected" equals `Vec$Int_String`
   - Expected: loader.global_symbols.has("Vec$Int_String") is false
   - Expected: loader.jit.stats().compile_count equals `0`
   - Expected: loader.jit.stats().cached_count equals `0`
   - Expected: loader.stats().symbol_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
expect(loader.config.enable_jit).to_equal(true)
val result = loader.resolve_generic("Vec", [make_named_type("Int"), make_named_type("String")])

match result:
    case SymbolResult.NotFound(name):
        expect(name).to_equal("Vec$Int_String")
    case _:
        expect("unexpected").to_equal("Vec$Int_String")

expect(loader.global_symbols.has("Vec$Int_String")).to_equal(false)
expect(loader.jit.stats().compile_count).to_equal(0)
expect(loader.jit.stats().cached_count).to_equal(0)
expect(loader.stats().symbol_count).to_equal(0)
```

</details>

#### resolves Vec i64 through the generic loader API

- var loader = ModuleLoader with defaults
- loader jit set metadata for test
   - Expected: symbol.name equals `Vec$i64`
   - Expected: symbol.is_jit is true
   - Expected: "missing" equals `Vec$i64`
   - Expected: loader.global_symbols.has("Vec$i64") is true
   - Expected: loader.jit.stats().compile_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "Vec$i64"
)
loader.jit.set_metadata_for_test(path, LoadedMetadata(possible: [entry], instantiations: []))

val result = loader.resolve_generic("Vec", [make_named_type("i64")])
match result:
    case SymbolResult.JitCompiled(symbol, code):
        expect(symbol.name).to_equal("Vec$i64")
        expect(symbol.is_jit).to_equal(true)
        expect(code.len()).to_be_greater_than(0)
    case _:
        expect("missing").to_equal("Vec$i64")

expect(loader.global_symbols.has("Vec$i64")).to_equal(true)
expect(loader.jit.stats().compile_count).to_equal(1)
```

</details>

#### unloads modules and drops their JIT-owned symbols

- var loader = ModuleLoader with defaults
- loader jit set metadata for test
-   = loader load
-   = loader resolve symbol
- loader unload
   - Expected: loader.is_loaded(path) is false
   - Expected: name equals `hot_reload_fn`
   - Expected: "stale" equals `hot_reload_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val entry = PossibleInstantiation(
    template_name: "Hot",
    type_args: "reload",
    mangled_name: "hot_reload_fn"
)
loader.jit.set_metadata_for_test(path, LoadedMetadata(possible: [entry], instantiations: []))
_ = loader.load(path)
_ = loader.resolve_symbol("hot_reload_fn")

loader.unload(path)

expect(loader.is_loaded(path)).to_equal(false)
match loader.resolve_symbol("hot_reload_fn"):
    case SymbolResult.NotFound(name):
        expect(name).to_equal("hot_reload_fn")
    case _:
        expect("stale").to_equal("hot_reload_fn")
```

</details>

#### unloads metadata-owned jit symbols even after owner drifted to __jit__

- var loader = ModuleLoader with defaults
-   = loader load
- loader jit exec mapper set record
- loader jit set cache for test
   - Expected: symbol.name equals `symbol_name`
   - Expected: "missing" equals `symbol_name`
- loader unload
   - Expected: loader.global_symbols.has(symbol_name) is false
   - Expected: name equals `symbol_name`
   - Expected: "stale" equals `symbol_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val symbol_name = "Vec$i64"
_ = loader.load(path)
loader.jit.set_metadata_for_test(
    path,
    LoadedMetadata(
        possible: [],
        instantiations: [
            InstantiationRecord(
                id: 0,
                template_name: "Vec",
                type_args: "i64",
                mangled_name: symbol_name,
                from_file: path,
                from_loc: path + ":0:0",
                to_obj: "jit_obj",
                status: "jit_compiled"
            )
        ]
    )
)
loader.jit.exec_mapper.set_record(symbol_name, "__jit__", 4096)
loader.jit.set_cache_for_test(symbol_name, [1, 2, 3], 4096)

match loader.resolve_symbol(symbol_name):
    case SymbolResult.JitCompiled(symbol, _):
        expect(symbol.name).to_equal(symbol_name)
    case _:
        expect("missing").to_equal(symbol_name)

loader.unload(path)

expect(loader.global_symbols.has(symbol_name)).to_equal(false)
match loader.resolve_symbol(symbol_name):
    case SymbolResult.NotFound(name):
        expect(name).to_equal(symbol_name)
    case _:
        expect("stale").to_equal(symbol_name)
```

</details>

#### unload removes owned globals, clears metadata-owned jit symbols, preserves unrelated globals, and clears loaded metadata

- var loader = ModuleLoader with defaults
-   = loader load
- owned symbol name:
- unrelated symbol name:
- loader jit exec mapper set record
- loader jit set cache for test
   - Expected: symbol.name equals `jit_symbol_name`
   - Expected: "missing" equals `jit_symbol_name`
- loader unload
   - Expected: loader.global_symbols.has(owned_symbol_name) is false
   - Expected: loader.global_symbols.has(jit_symbol_name) is false
   - Expected: loader.global_symbols.has(unrelated_symbol_name) is true
   - Expected: loader.jit.loaded_metadata.has(path) is false
   - Expected: loader.jit.jit_cache.has(jit_symbol_name) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val unrelated_path = second_module_path()
val owned_symbol_name = "module_owned_fn"
val unrelated_symbol_name = "other_module_fn"
val jit_symbol_name = "Vec$i64"
_ = loader.load(path)

val owned_symbol = LoadedSymbol(
    name: owned_symbol_name,
    address: 12288,
    size: 16,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val unrelated_symbol = LoadedSymbol(
    name: unrelated_symbol_name,
    address: 16384,
    size: 16,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
loader.global_symbols = {
    owned_symbol_name: (path, owned_symbol),
    unrelated_symbol_name: (unrelated_path, unrelated_symbol)
}
loader.jit.set_metadata_for_test(
    path,
    LoadedMetadata(
        possible: [],
        instantiations: [
            InstantiationRecord(
                id: 0,
                template_name: "Vec",
                type_args: "i64",
                mangled_name: jit_symbol_name,
                from_file: path,
                from_loc: path + ":0:0",
                to_obj: "jit_obj",
                status: "jit_compiled"
            )
        ]
    )
)
loader.jit.exec_mapper.set_record(jit_symbol_name, "__jit__", 20480)
loader.jit.set_cache_for_test(jit_symbol_name, [1, 2, 3], 20480)

match loader.resolve_symbol(jit_symbol_name):
    case SymbolResult.JitCompiled(symbol, _):
        expect(symbol.name).to_equal(jit_symbol_name)
    case _:
        expect("missing").to_equal(jit_symbol_name)

loader.unload(path)

expect(loader.global_symbols.has(owned_symbol_name)).to_equal(false)
expect(loader.global_symbols.has(jit_symbol_name)).to_equal(false)
expect(loader.global_symbols.has(unrelated_symbol_name)).to_equal(true)
expect(loader.jit.loaded_metadata.has(path)).to_equal(false)
expect(loader.jit.jit_cache.has(jit_symbol_name)).to_equal(false)
```

</details>

#### impl-method unload clears modules entry for the path

- var loader = ModuleLoader with defaults
-   = loader load
   - Expected: loader.is_loaded(path) is true
- loader unload
   - Expected: loader.is_loaded(path) is false
   - Expected: loader.modules.has(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
_ = loader.load(path)
expect(loader.is_loaded(path)).to_equal(true)

loader.unload(path)

expect(loader.is_loaded(path)).to_equal(false)
expect(loader.modules.has(path)).to_equal(false)
```

</details>

#### impl-method unload drops global symbols owned by that module

- var loader = ModuleLoader with defaults
-   = loader load
- loader global symbols = {"owned sym":
- loader unload
   - Expected: loader.global_symbols.has("owned_sym") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
_ = loader.load(path)
val sym = LoadedSymbol(
    name: "owned_sym",
    address: 8192,
    size: 8,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
loader.global_symbols = {"owned_sym": (path, sym)}

loader.unload(path)

expect(loader.global_symbols.has("owned_sym")).to_equal(false)
```

</details>

#### impl-method unload clears loaded_metadata for the path

- var loader = ModuleLoader with defaults
- loader jit set metadata for test
-   = loader load
- loader unload
   - Expected: loader.jit.loaded_metadata.has(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "vec_runtime_i64"
)
loader.jit.set_metadata_for_test(path, LoadedMetadata(possible: [entry], instantiations: []))
_ = loader.load(path)

loader.unload(path)

expect(loader.jit.loaded_metadata.has(path)).to_equal(false)
```

</details>

#### impl-method unload clears jit_cache entries for symbols of the module

- var loader = ModuleLoader with defaults
-   = loader load
- loader jit exec mapper set record
- loader jit set cache for test
-   = loader resolve symbol
- loader unload
   - Expected: loader.jit.jit_cache.has(sym_name) is false
   - Expected: loader.global_symbols.has(sym_name) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val sym_name = "Vec$i64"
_ = loader.load(path)
loader.jit.set_metadata_for_test(
    path,
    LoadedMetadata(
        possible: [],
        instantiations: [
            InstantiationRecord(
                id: 0,
                template_name: "Vec",
                type_args: "i64",
                mangled_name: sym_name,
                from_file: path,
                from_loc: path + ":0:0",
                to_obj: "jit_obj",
                status: "jit_compiled"
            )
        ]
    )
)
loader.jit.exec_mapper.set_record(sym_name, "__jit__", 4096)
loader.jit.set_cache_for_test(sym_name, [1, 2, 3], 4096)
_ = loader.resolve_symbol(sym_name)

loader.unload(path)

expect(loader.jit.jit_cache.has(sym_name)).to_equal(false)
expect(loader.global_symbols.has(sym_name)).to_equal(false)
```

</details>

#### impl-method unload preserves global symbols owned by a different module

- var loader = ModuleLoader with defaults
-   = loader load
- loader global symbols = {"other fn":
- loader unload
   - Expected: loader.global_symbols.has("other_fn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val other_path = second_module_path()
_ = loader.load(path)
val other_sym = LoadedSymbol(
    name: "other_fn",
    address: 32768,
    size: 8,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
loader.global_symbols = {"other_fn": (other_path, other_sym)}

loader.unload(path)

expect(loader.global_symbols.has("other_fn")).to_equal(true)
```

</details>

#### impl-method unload of a never-loaded path is a no-op and does not panic

- var loader = ModuleLoader with defaults
- loader unload
   - Expected: loader.modules.has(phantom) is false
   - Expected: loader.global_symbols.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val phantom = "test/unit/compiler/loader/does_not_exist_ghost.spl"

loader.unload(phantom)

expect(loader.modules.has(phantom)).to_equal(false)
expect(loader.global_symbols.len()).to_equal(0)
```

</details>

#### impl-method double-unload is idempotent: second call is a no-op

- var loader = ModuleLoader with defaults
-   = loader load
- loader global symbols = {"idempotent sym":
- loader unload
- loader unload
   - Expected: loader.is_loaded(path) is false
   - Expected: loader.global_symbols.has("idempotent_sym") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
_ = loader.load(path)
val sym = LoadedSymbol(
    name: "idempotent_sym",
    address: 4096,
    size: 8,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
loader.global_symbols = {"idempotent_sym": (path, sym)}

loader.unload(path)
loader.unload(path)

expect(loader.is_loaded(path)).to_equal(false)
expect(loader.global_symbols.has("idempotent_sym")).to_equal(false)
```

</details>

#### impl-method unload produces identical module-table state across loaders

- var loader a = ModuleLoader with defaults
- var loader b = ModuleLoader with defaults
-   = loader a load
-   = loader b load
- loader a global symbols = {sym name:
- loader b global symbols = {sym name:
- loader a unload
- loader b unload
   - Expected: loader_a.is_loaded(path) equals `loader_b.is_loaded(path)`
   - Expected: loader_a.global_symbols.has(sym_name) equals `loader_b.global_symbols.has(sym_name)`
   - Expected: loader_a.global_symbols.len() equals `loader_b.global_symbols.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader_a = ModuleLoader.with_defaults()
var loader_b = ModuleLoader.with_defaults()
val path = existing_module_path()
val sym_name = "parity_sym"

_ = loader_a.load(path)
_ = loader_b.load(path)

val sym_a = LoadedSymbol(
    name: sym_name,
    address: 8192,
    size: 8,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
val sym_b = LoadedSymbol(
    name: sym_name,
    address: 8192,
    size: 8,
    ty: SymbolType.Function,
    is_jit: false,
    file_offset: 0
)
loader_a.global_symbols = {sym_name: (path, sym_a)}
loader_b.global_symbols = {sym_name: (path, sym_b)}

loader_a.unload(path)
loader_b.unload(path)

# Observable state must be identical
expect(loader_a.is_loaded(path)).to_equal(loader_b.is_loaded(path))
expect(loader_a.global_symbols.has(sym_name)).to_equal(loader_b.global_symbols.has(sym_name))
expect(loader_a.global_symbols.len()).to_equal(loader_b.global_symbols.len())
```

</details>

#### impl-method unload after JIT symbols are registered removes them correctly

- var loader = ModuleLoader with defaults
- loader jit set metadata for test
-   = loader load
-   = loader resolve symbol
- loader unload
   - Expected: loader.global_symbols.has(jit_sym) is false
   - Expected: name equals `jit_sym`
   - Expected: "still_present" equals `jit_sym`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val jit_sym = "jit_owned_fn"
val entry = PossibleInstantiation(
    template_name: "JitOwned",
    type_args: "f64",
    mangled_name: jit_sym
)
loader.jit.set_metadata_for_test(path, LoadedMetadata(possible: [entry], instantiations: []))
_ = loader.load(path)
_ = loader.resolve_symbol(jit_sym)

loader.unload(path)

expect(loader.global_symbols.has(jit_sym)).to_equal(false)
match loader.resolve_symbol(jit_sym):
    case SymbolResult.NotFound(name):
        expect(name).to_equal(jit_sym)
    case _:
        expect("still_present").to_equal(jit_sym)
```

</details>

#### reload rehydrates on-disk metadata so persisted jit symbols stay resolvable

- var loader = ModuleLoader with defaults
   - Expected: module.path equals `path`
   - Expected: "unexpected" equals `path`
   - Expected: loader.jit.loaded_metadata.has(path) is true
   - Expected: symbol.name equals `persisted_symbol`
   - Expected: symbol.name equals `persisted_symbol`
   - Expected: "missing" equals `persisted_symbol`
   - Expected: module.path equals `path`
   - Expected: "unexpected" equals `path`
   - Expected: loader.jit.loaded_metadata.has(path) is true
   - Expected: symbol.name equals `persisted_symbol`
   - Expected: symbol.name equals `persisted_symbol`
   - Expected: "missing" equals `persisted_symbol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loader = ModuleLoader.with_defaults()
val path = existing_module_path()
val persisted_symbol = "Vec$i64"

match loader.load(path):
    case LoadResult.Success(module):
        expect(module.path).to_equal(path)
    case _:
        expect("unexpected").to_equal(path)

expect(loader.jit.loaded_metadata.has(path)).to_equal(true)

match loader.resolve_symbol(persisted_symbol):
    case SymbolResult.JitCompiled(symbol, code):
        expect(symbol.name).to_equal(persisted_symbol)
        expect(code.len()).to_be_greater_than(0)
    case SymbolResult.Found(symbol, _):
        expect(symbol.name).to_equal(persisted_symbol)
    case _:
        expect("missing").to_equal(persisted_symbol)

match moduleloader_reload(loader, path):
    case LoadResult.Success(module):
        expect(module.path).to_equal(path)
    case _:
        expect("unexpected").to_equal(path)

expect(loader.jit.loaded_metadata.has(path)).to_equal(true)
match loader.resolve_symbol(persisted_symbol):
    case SymbolResult.JitCompiled(symbol, code):
        expect(symbol.name).to_equal(persisted_symbol)
        expect(code.len()).to_be_greater_than(0)
    case SymbolResult.Found(symbol, _):
        expect(symbol.name).to_equal(persisted_symbol)
    case _:
        expect("missing").to_equal(persisted_symbol)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
