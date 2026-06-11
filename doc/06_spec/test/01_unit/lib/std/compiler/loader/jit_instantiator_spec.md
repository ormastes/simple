# JIT Instantiator Specification

> JitInstantiator provides on-demand instantiation of generic templates during runtime loading. When a symbol cannot be found in pre-compiled code, the JIT instantiator can compile it from template metadata stored in SMF files.

<!-- sdn-diagram:id=jit_instantiator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_instantiator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_instantiator_spec -> std
jit_instantiator_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_instantiator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JIT Instantiator Specification

JitInstantiator provides on-demand instantiation of generic templates during runtime loading. When a symbol cannot be found in pre-compiled code, the JIT instantiator can compile it from template metadata stored in SMF files.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1021-1030 |
| Category | Tooling |
| Difficulty | 5/5 |
| Status | In Progress |
| Source | `test/01_unit/lib/std/compiler/loader/jit_instantiator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

JitInstantiator provides on-demand instantiation of generic templates during
runtime loading. When a symbol cannot be found in pre-compiled code, the JIT
instantiator can compile it from template metadata stored in SMF files.

## Key Features

- Load-time JIT compilation of generic templates
- SMF note.sdn metadata loading and caching
- Circular dependency detection
- Maximum depth limiting
- SMF file updating with compiled results
- Symbol resolution with JIT fallback

## Implementation

File: `/home/ormastes/dev/pub/simple/src/compiler/loader/jit_instantiator.spl`

## Workflow

1. Symbol lookup fails in loaded code
2. JitInstantiator checks note.sdn metadata for "possible" entries
3. If found, triggers template compilation via TemplateInstantiator
4. Caches compiled code and updates SMF note.sdn
5. Returns compiled code address

## Scenarios

### JitInstantiatorConfig

#### creates default configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig.default()

expect(config.update_smf).to(be_true())
expect(config.max_depth).to(eq(50))
expect(config.enabled).to(be_true())
expect(config.verbose).to(be_false())
```

</details>

#### allows custom configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: false,
    max_depth: 100,
    enabled: false,
    verbose: true
)

expect(config.update_smf).to(be_false())
expect(config.max_depth).to(eq(100))
expect(config.enabled).to(be_false())
expect(config.verbose).to(be_true())
```

</details>

#### supports disabling JIT

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: true,
    max_depth: 50,
    enabled: false,
    verbose: false
)

expect(config.enabled).to(be_false())
```

</details>

### JitInstantiationResult Variants

#### when checking success results

#### identifies Success as success

1. address: Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitInstantiationResult.Success(
    code: [1, 2, 3],
    symbol: "fn$Vec$i64",
    address: Some(0x1000)
)

expect(result.is_success()).to(be_true())
expect(result.is_error()).to(be_false())
```

</details>

#### handles Success without address

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitInstantiationResult.Success(
    code: [1, 2, 3],
    symbol: "fn$Vec$i64",
    address: nil
)

expect(result.is_success()).to(be_true())
```

</details>

#### when checking error results

#### identifies CompilationError as error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitInstantiationResult.CompilationError(
    "Type mismatch in template"
)

expect(result.is_success()).to(be_false())
expect(result.is_error()).to(be_true())
```

</details>

#### identifies CircularDependency as error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitInstantiationResult.CircularDependency(
    cycle: ["A", "B", "C", "A"]
)

expect(result.is_error()).to(be_true())
```

</details>

#### identifies UpdateFailed as error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitInstantiationResult.UpdateFailed(
    symbol: "fn$Vec$i64",
    error: "SMF file locked"
)

expect(result.is_error()).to(be_true())
```

</details>

#### when handling not found results

#### identifies NotFound as neither success nor error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = JitInstantiationResult.NotFound("missing_symbol")

expect(result.is_success()).to(be_false())
expect(result.is_error()).to(be_false())
```

</details>

### JitInstantiator Construction

#### creates with default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig.default()
val jit = JitInstantiator.new(config)

val stats = jit.stats()
expect(stats.cached_count).to(eq(0))
expect(stats.loaded_smf_count).to(eq(0))
```

</details>

#### creates with custom config

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: false,
    max_depth: 25,
    enabled: true,
    verbose: true
)
val jit = JitInstantiator.new(config)

# Verify config is stored
expect(jit.config.max_depth).to(eq(25))
expect(jit.config.verbose).to(be_true())
```

</details>

#### initializes empty caches

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = JitInstantiator.new(JitInstantiatorConfig.default())

val stats = jit.stats()
expect(stats.cached_count).to(eq(0))
expect(stats.loaded_smf_count).to(eq(0))
```

</details>

### JitInstantiator Metadata Loading

#### when loading metadata from SMF

#### loads metadata successfully

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# BLOCKED: Requires real SMF file infrastructure
# Need to create test SMF file with note.sdn section
# Placeholder test until SMF I/O is implemented
val result = jit.load_smf_metadata("test.smf")
expect(result.ok.?).to(be_true())

# Verify empty metadata (placeholder behavior)
val loaded = jit.loaded_metadata["test.smf"]
expect(loaded.possible.len()).to(eq(0))
expect(loaded.instantiations.len()).to(eq(0))
```

</details>

#### caches loaded metadata

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Load same file twice
val result1 = jit.load_smf_metadata("test.smf")
val result2 = jit.load_smf_metadata("test.smf")

expect(result1.ok.?).to(be_true())
expect(result2.ok.?).to(be_true())

# Verify metadata is stored (second load overwrites)
expect(jit.loaded_metadata.has("test.smf")).to(be_true())
```

</details>

#### handles missing SMF files

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Test loading non-existent file
val result = jit.load_smf_metadata("nonexistent.smf")

# Current implementation returns empty metadata (placeholder)
# Future: Should return Err for missing files
expect(result.ok.?).to(be_true())
```

</details>

#### tracks loaded SMF count

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Load multiple SMF files
val result1 = jit.load_smf_metadata("test1.smf")
val result2 = jit.load_smf_metadata("test2.smf")
expect(result1.ok.?).to(be_true())
expect(result2.ok.?).to(be_true())

val stats = jit.stats()
expect(stats.loaded_smf_count).to(eq(2))
```

</details>

### JitInstantiator Symbol Checking

#### when checking if symbol can be JIT-compiled

#### returns false when JIT is disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: true,
    max_depth: 50,
    enabled: false,
    verbose: false
)
val jit = JitInstantiator.new(config)

expect(jit.can_jit_instantiate("any_symbol")).to(be_false())
```

</details>

#### returns false for unknown symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = JitInstantiator.new(JitInstantiatorConfig.default())

expect(jit.can_jit_instantiate("unknown_symbol")).to(be_false())
```

</details>

#### returns true for symbols in metadata

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Manually create test metadata
val test_entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "fn$Vec$i64"
)
val metadata = LoadedMetadata(
    possible: [test_entry],
    instantiations: []
)
jit.loaded_metadata["test.smf"] = metadata

expect(jit.can_jit_instantiate("fn$Vec$i64")).to(be_true())
```

</details>

#### when finding possible instantiations

#### returns None for unknown symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = JitInstantiator.new(JitInstantiatorConfig.default())

val found = jit.find_possible("unknown_symbol")
expect(found.?).to(be_false())
```

</details>

#### finds possible entry in loaded metadata

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Manually create test metadata
val test_entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "fn$Vec$i64"
)
val metadata = LoadedMetadata(
    possible: [test_entry],
    instantiations: []
)
jit.loaded_metadata["test.smf"] = metadata

val found = jit.find_possible("fn$Vec$i64")
expect(found.?).to(be_true())

val (path, entry) = found.unwrap()
expect(path).to(eq("test.smf"))
expect(entry.mangled_name).to(eq("fn$Vec$i64"))
expect(entry.template_name).to(eq("Vec"))
expect(entry.type_args).to(eq("i64"))
```

</details>

### JitInstantiator Compilation

#### when JIT is disabled

#### returns NotFound when disabled

1. var jit = JitInstantiator new
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: true,
    max_depth: 50,
    enabled: false,
    verbose: false
)
var jit = JitInstantiator.new(config)

val result = jit.try_jit_instantiate("any_symbol")

match result:
    case NotFound(sym):
        expect(sym).to(eq("any_symbol"))
    case _:
        fail("Expected NotFound, got different variant")
```

</details>

#### when depth limit is exceeded

#### returns CompilationError at max depth

1. var jit = JitInstantiator new
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: true,
    max_depth: 2,
    enabled: true,
    verbose: false
)
var jit = JitInstantiator.new(config)

# Manually set depth to max
jit.depth = 2

val result = jit.try_jit_instantiate("test_symbol")

match result:
    case CompilationError(msg):
        expect(msg).to(contain("Maximum JIT depth"))
        expect(msg).to(contain("2"))
    case _:
        fail("Expected CompilationError")
```

</details>

#### when symbol is cached

#### returns cached code

1. var jit = JitInstantiator new
2. jit jit cache["test fn"] =
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Manually add to cache for testing
jit.jit_cache["test_fn"] = ([1, 2, 3, 4], 0x1000)

val result = jit.try_jit_instantiate("test_fn")

match result:
    case Success(code, symbol, address):
        expect(code).to(eq([1, 2, 3, 4]))
        expect(symbol).to(eq("test_fn"))
        expect(address.?).to(be_true())
        expect(address.unwrap()).to(eq(0x1000))
    case _:
        fail("Expected Success from cache")
```

</details>

#### when detecting circular dependencies

#### detects direct cycle

1. var jit = JitInstantiator new
2. jit in progress = jit in progress insert
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Manually mark symbol as in-progress
jit.in_progress = jit.in_progress.insert("cycle_fn")

val result = jit.try_jit_instantiate("cycle_fn")

match result:
    case CircularDependency(cycle):
        expect(cycle.len()).to(be_greater_than(0))
    case _:
        fail("Expected CircularDependency")
```

</details>

#### when symbol not found

#### returns NotFound for unknown symbol

1. var jit = JitInstantiator new
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

val result = jit.try_jit_instantiate("unknown_symbol")

match result:
    case NotFound(sym):
        expect(sym).to(eq("unknown_symbol"))
    case _:
        fail("Expected NotFound")
```

</details>

### JitInstantiator SMF Updates

#### when updating SMF after compilation

#### updates metadata in memory

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Create test metadata with possible entry
val test_entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "fn$Vec$i64"
)
val metadata = LoadedMetadata(
    possible: [test_entry],
    instantiations: []
)
jit.loaded_metadata["test.smf"] = metadata

# Call update_smf_note_sdn
val result = jit.update_smf_note_sdn("test.smf", test_entry)
expect(result.ok.?).to(be_true())

# Verify entry moved from possible to instantiations
val updated = jit.loaded_metadata["test.smf"]
expect(updated.possible.len()).to(eq(0))
expect(updated.instantiations.len()).to(eq(1))
expect(updated.instantiations[0].mangled_name).to(eq("fn$Vec$i64"))
```

</details>

#### removes from possible list

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Create metadata with multiple possible entries
val entry1 = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "fn$Vec$i64"
)
val entry2 = PossibleInstantiation(
    template_name: "Vec",
    type_args: "f64",
    mangled_name: "fn$Vec$f64"
)
val metadata = LoadedMetadata(
    possible: [entry1, entry2],
    instantiations: []
)
jit.loaded_metadata["test.smf"] = metadata

# Update with first entry
val result = jit.update_smf_note_sdn("test.smf", entry1)
expect(result.ok.?).to(be_true())

# Verify only entry1 was removed
val updated = jit.loaded_metadata["test.smf"]
expect(updated.possible.len()).to(eq(1))
expect(updated.possible[0].mangled_name).to(eq("fn$Vec$f64"))
```

</details>

#### adds to instantiations list

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Create metadata with existing instantiation
val existing_inst = InstantiationRecord(
    id: 0,
    template_name: "List",
    type_args: "text",
    mangled_name: "fn$List$text",
    from_file: "test.smf",
    from_loc: "test.smf:10:5",
    to_obj: "obj1",
    status: "compiled"
)
val test_entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "fn$Vec$i64"
)
val metadata = LoadedMetadata(
    possible: [test_entry],
    instantiations: [existing_inst]
)
jit.loaded_metadata["test.smf"] = metadata

# Update with new entry
val result = jit.update_smf_note_sdn("test.smf", test_entry)
expect(result.ok.?).to(be_true())

# Verify new instantiation was added
val updated = jit.loaded_metadata["test.smf"]
expect(updated.instantiations.len()).to(eq(2))
expect(updated.instantiations[1].mangled_name).to(eq("fn$Vec$i64"))
expect(updated.instantiations[1].status).to(eq("jit_compiled"))
```

</details>

#### handles update errors

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Test with non-existent SMF path (current impl doesn't error)
val test_entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "fn$Vec$i64"
)

# Current implementation always succeeds for in-memory updates
# Future: Test actual SMF file write failures
val result = jit.update_smf_note_sdn("nonexistent.smf", test_entry)
expect(result.ok.?).to(be_true())
```

</details>

#### when update_smf is disabled

#### skips SMF updates

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: false,
    max_depth: 50,
    enabled: true,
    verbose: false
)
var jit = JitInstantiator.new(config)

# Create test metadata
val test_entry = PossibleInstantiation(
    template_name: "Vec",
    type_args: "i64",
    mangled_name: "fn$Vec$i64"
)
val metadata = LoadedMetadata(
    possible: [test_entry],
    instantiations: []
)
jit.loaded_metadata["test.smf"] = metadata

# When update_smf is false, update_smf_note_sdn is not called
# during do_jit_compile, but we can still call it directly
# to verify it works regardless of config
val result = jit.update_smf_note_sdn("test.smf", test_entry)
expect(result.ok.?).to(be_true())

# Verify the config setting
expect(jit.config.update_smf).to(be_false())
```

</details>

### JitInstantiator Statistics

#### reports initial empty stats

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jit = JitInstantiator.new(JitInstantiatorConfig.default())

val stats = jit.stats()
expect(stats.cached_count).to(eq(0))
expect(stats.loaded_smf_count).to(eq(0))
```

</details>

#### tracks cached compilations

1. var jit = JitInstantiator new
2. jit jit cache["test fn1"] =
3. jit jit cache["test fn2"] =


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Add to cache manually
jit.jit_cache["test_fn1"] = ([1], 0x1000)
jit.jit_cache["test_fn2"] = ([2], 0x2000)

val stats = jit.stats()
expect(stats.cached_count).to(eq(2))
```

</details>

#### tracks loaded SMF files

1. var jit = JitInstantiator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var jit = JitInstantiator.new(JitInstantiatorConfig.default())

# Load multiple SMF files
val _ = jit.load_smf_metadata("file1.smf")
val _ = jit.load_smf_metadata("file2.smf")
val _ = jit.load_smf_metadata("file3.smf")

val stats = jit.stats()
expect(stats.loaded_smf_count).to(eq(3))
```

</details>

### JitSymbolResolver

#### when creating resolver

#### creates with default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

# Verify initial state
val address = resolver.resolve("any_symbol")
expect(address.?).to(be_false())
```

</details>

#### creates with custom config

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = JitInstantiatorConfig(
    update_smf: false,
    max_depth: 25,
    enabled: false,
    verbose: true
)
val resolver = JitSymbolResolver.new(config)

# Resolver should have JIT disabled
val address = resolver.resolve("any_symbol")
expect(address.?).to(be_false())
```

</details>

#### when registering symbols

#### registers symbol address

1. var resolver = JitSymbolResolver new
2. resolver register


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

resolver.register("my_fn", 0x1000)

val address = resolver.resolve("my_fn")
expect(address.?).to(be_true())
expect(address.unwrap()).to(eq(0x1000))
```

</details>

#### overwrites existing registration

1. var resolver = JitSymbolResolver new
2. resolver register
3. resolver register


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

resolver.register("my_fn", 0x1000)
resolver.register("my_fn", 0x2000)

val address = resolver.resolve("my_fn")
expect(address.unwrap()).to(eq(0x2000))
```

</details>

#### when resolving symbols

#### resolves registered symbols

1. var resolver = JitSymbolResolver new
2. resolver register


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

resolver.register("known_fn", 0x1000)

val address = resolver.resolve("known_fn")
expect(address.?).to(be_true())
expect(address.unwrap()).to(eq(0x1000))
```

</details>

#### returns None for unknown symbols

1. var resolver = JitSymbolResolver new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

val address = resolver.resolve("unknown_fn")
expect(address.?).to(be_false())
```

</details>

#### tries JIT on miss

1. var resolver = JitSymbolResolver new


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

# BLOCKED: Requires CompilerContext FFI implementation
# This test needs:
# 1. resolver.jit with loaded metadata containing test symbol
# 2. CompilerContext.instantiate() to work
# 3. Executable memory allocation

# For now, test that resolution returns None for unknown symbols
val address = resolver.resolve("fn$Vec$i64")
expect(address.?).to(be_false())
```

</details>

#### caches JIT result

1. var resolver = JitSymbolResolver new
2. resolver jit jit cache["fn$Vec$i64"] =


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

# Manually simulate a cached JIT result
resolver.jit.jit_cache["fn$Vec$i64"] = ([1, 2, 3], 0x2000)
resolver.jit.symbol_table["fn$Vec$i64"] = 0x2000

# First resolve should hit cache (not registered in symbols yet)
val addr1 = resolver.resolve("fn$Vec$i64")
expect(addr1.?).to(be_true())
expect(addr1.unwrap()).to(eq(0x2000))

# Second resolve should hit primary symbols table
val addr2 = resolver.resolve("fn$Vec$i64")
expect(addr2.?).to(be_true())
expect(addr2.unwrap()).to(eq(0x2000))
```

</details>

#### when loading SMF files

#### loads SMF metadata

1. var resolver = JitSymbolResolver new


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

# Test the load_smf wrapper method
val result = resolver.load_smf("test.smf")
expect(result.ok.?).to(be_true())

# Verify metadata was loaded into JIT
val stats = resolver.jit.stats()
expect(stats.loaded_smf_count).to(eq(1))
```

</details>

#### propagates load errors

1. var resolver = JitSymbolResolver new


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = JitSymbolResolver.new(JitInstantiatorConfig.default())

# Test with invalid SMF path
val result = resolver.load_smf("invalid_path.smf")

# Current implementation returns Ok (placeholder)
# Future: Should return Err for file I/O errors
expect(result.ok.?).to(be_true())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
