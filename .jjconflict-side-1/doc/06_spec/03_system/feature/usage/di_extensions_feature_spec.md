# DI Extensions Feature

> Tests the DI Extension Container (CompileContext.extensions) which provides a dynamic plugin/extension registration point separate from typed core services. Covers basic plugin registration and retrieval, multiple independent plugins, separation from core services, integration with CompileContext, and plugin lifecycle management including lock/unlock behavior.

<!-- sdn-diagram:id=di_extensions_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_extensions_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_extensions_feature_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_extensions_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DI Extensions Feature

Tests the DI Extension Container (CompileContext.extensions) which provides a dynamic plugin/extension registration point separate from typed core services. Covers basic plugin registration and retrieval, multiple independent plugins, separation from core services, integration with CompileContext, and plugin lifecycle management including lock/unlock behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/usage/di_extensions_feature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the DI Extension Container (CompileContext.extensions) which provides a dynamic
plugin/extension registration point separate from typed core services. Covers basic
plugin registration and retrieval, multiple independent plugins, separation from core
services, integration with CompileContext, and plugin lifecycle management including
lock/unlock behavior.

## Scenarios

### DI Extensions Feature: Phase 1 - Basic plugin registration

#### can register a plugin by name

1. ext bind instance
   - Expected: ext.has("Profiler") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("Profiler", "profiler-v1")
expect(ext.has("Profiler")).to_equal(true)
```

</details>

#### can retrieve a registered plugin

1. ext bind instance
   - Expected: result equals `fmt-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("Formatter", "fmt-plugin")
val result = ext.resolve("Formatter")
expect(result).to_equal("fmt-plugin")
```

</details>

#### unregistered plugin returns nil via resolve_or

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("MissingPlugin", nil)
expect(result).to_be_nil()
```

</details>

#### unregistered plugin returns default via resolve_or

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("MissingPlugin", "default-value")
expect(result).to_equal("default-value")
```

</details>

#### has returns false for unregistered plugin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.has("NotHere")).to_equal(false)
```

</details>

#### has returns true after registration

1. ext bind instance
   - Expected: ext.has("MyPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("MyPlugin", "v1")
expect(ext.has("MyPlugin")).to_equal(true)
```

</details>

#### can register integer plugin value

1. ext bind instance
   - Expected: result equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("MaxWorkers", 8)
val result = ext.resolve("MaxWorkers")
expect(result).to_equal(8)
```

</details>

#### can register boolean plugin value

1. ext bind instance
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("DebugMode", true)
val result = ext.resolve("DebugMode")
expect(result).to_equal(true)
```

</details>

### DI Extensions Feature: Phase 2 - Multiple plugins

#### can register multiple independent plugins

1. ext bind instance
2. ext bind instance
   - Expected: ext.has("PluginA") is true
   - Expected: ext.has("PluginB") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("PluginA", "alpha")
ext.bind_instance("PluginB", "beta")
expect(ext.has("PluginA")).to_equal(true)
expect(ext.has("PluginB")).to_equal(true)
```

</details>

#### plugins do not interfere with each other

1. ext bind instance
   - Expected: x equals `x-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("PluginX", "x-value")
val other = ext.resolve_or("PluginY", nil)
expect(other).to_be_nil()
val x = ext.resolve("PluginX")
expect(x).to_equal("x-value")
```

</details>

#### can overwrite an existing plugin registration

1. ext bind instance
2. ext bind instance
   - Expected: result equals `v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("Plugin", "v1")
ext.bind_instance("Plugin", "v2")
val result = ext.resolve("Plugin")
expect(result).to_equal("v2")
```

</details>

#### resolves three plugins independently

1. ext bind instance
2. ext bind instance
3. ext bind instance
   - Expected: ext.resolve("A") equals `alpha`
   - Expected: ext.resolve("B") equals `beta`
   - Expected: ext.resolve("C") equals `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("A", "alpha")
ext.bind_instance("B", "beta")
ext.bind_instance("C", "gamma")
expect(ext.resolve("A")).to_equal("alpha")
expect(ext.resolve("B")).to_equal("beta")
expect(ext.resolve("C")).to_equal("gamma")
```

</details>

#### factory and instance bindings coexist

1. ext bind
2. ext bind instance
   - Expected: ext.resolve("LazyPlugin") equals `lazy-value`
   - Expected: ext.resolve("EagerPlugin") equals `eager-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind("LazyPlugin", fn(): "lazy-value")
ext.bind_instance("EagerPlugin", "eager-value")
expect(ext.resolve("LazyPlugin")).to_equal("lazy-value")
expect(ext.resolve("EagerPlugin")).to_equal("eager-value")
```

</details>

#### resolves two plugins after separate registration

1. ext bind instance
2. ext bind instance
   - Expected: a equals `value-a`
   - Expected: b equals `value-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("PluginA", "value-a")
ext.bind_instance("PluginB", "value-b")
val a = ext.resolve("PluginA")
val b = ext.resolve("PluginB")
expect(a).to_equal("value-a")
expect(b).to_equal("value-b")
```

</details>

### DI Extensions Feature: Phase 3 - Separation from core services

#### extensions container starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.has("Backend")).to_equal(false)
expect(ext.has("Logger")).to_equal(false)
expect(ext.has("AnyPlugin")).to_equal(false)
```

</details>

#### extensions container is independent of typed backend port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val backend_in_ext = ext.resolve_or("Backend", nil)
expect(backend_in_ext).to_be_nil()
```

</details>

#### core services not accessible via extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val logger = ext.resolve_or("Logger", nil)
val parser = ext.resolve_or("Parser", nil)
val lexer = ext.resolve_or("Lexer", nil)
expect(logger).to_be_nil()
expect(parser).to_be_nil()
expect(lexer).to_be_nil()
```

</details>

#### factory-bound extension resolves lazily

1. ext bind
   - Expected: ext.has("LazyPlugin") is true
   - Expected: result equals `lazy-created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind("LazyPlugin", fn(): "lazy-created")
expect(ext.has("LazyPlugin")).to_equal(true)
val result = ext.resolve("LazyPlugin")
expect(result).to_equal("lazy-created")
```

</details>

#### profile is preserved on extensions container

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = DiContainer(bindings: [], singletons: [], profile: "prod", all_bindings: [], locked: false)
expect(ext.profile).to_equal("prod")
```

</details>

### DI Extensions Feature: Phase 4 - Integration with CompileContext

#### extensions container starts with empty bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
expect(extensions.has("AnyPlugin")).to_equal(false)
```

</details>

#### register_extension adds to extensions (via bind_instance)

1. extensions bind instance
   - Expected: extensions.has("MyPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_ext()
extensions.bind_instance("MyPlugin", "plugin-value")
expect(extensions.has("MyPlugin")).to_equal(true)
```

</details>

#### get_extension retrieves registered value (via resolve_or)

1. extensions bind instance
   - Expected: result equals `plugin-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_ext()
extensions.bind_instance("MyPlugin", "plugin-value")
val result = extensions.resolve_or("MyPlugin", nil)
expect(result).to_equal("plugin-value")
```

</details>

#### get_extension returns nil for unregistered (resolve_or nil default)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_ext()
val result = extensions.resolve_or("UnregisteredPlugin", nil)
expect(result).to_be_nil()
```

</details>

#### extensions uses profile from options

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = DiContainer(bindings: [], singletons: [], profile: "test", all_bindings: [], locked: false)
expect(extensions.profile).to_equal("test")
```

</details>

#### extensions starts unlocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = make_ext()
expect(extensions.is_locked()).to_equal(false)
```

</details>

### DI Extensions Feature: Phase 5 - Plugin lifecycle

#### plugin registration before lock succeeds

1. ext bind instance
   - Expected: ext.has("LifecyclePlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("LifecyclePlugin", "before-lock")
expect(ext.has("LifecyclePlugin")).to_equal(true)
```

</details>

#### plugin retrieval after lock works

1. ext bind instance
2. ext lock
   - Expected: result equals `before-lock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("LifecyclePlugin", "before-lock")
ext.lock()
val result = ext.resolve("LifecyclePlugin")
expect(result).to_equal("before-lock")
```

</details>

#### plugin registration after lock fails or is ignored

1. ext lock
2. ext bind instance
   - Expected: ext.has("PostLockPlugin") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
ext.bind_instance("PostLockPlugin", "should-not-register")
expect(ext.has("PostLockPlugin")).to_equal(false)
```

</details>

#### unlock allows plugin registration again

1. ext lock
2. ext bind instance
   - Expected: ext.has("TempPlugin") is false
3. ext unlock
4. ext bind instance
   - Expected: ext.has("TempPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
ext.bind_instance("TempPlugin", "v1")
expect(ext.has("TempPlugin")).to_equal(false)
ext.unlock()
ext.bind_instance("TempPlugin", "v1")
expect(ext.has("TempPlugin")).to_equal(true)
```

</details>

#### full plugin lifecycle: register, lock, resolve, unlock, re-register

1. ext bind instance
2. ext lock
   - Expected: ext.has("CorePlugin") is true
   - Expected: result equals `core-v1`
3. ext unlock
4. ext bind instance
   - Expected: ext.has("NewPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("CorePlugin", "core-v1")
ext.lock()
expect(ext.has("CorePlugin")).to_equal(true)
val result = ext.resolve("CorePlugin")
expect(result).to_equal("core-v1")
ext.unlock()
ext.bind_instance("NewPlugin", "new-v1")
expect(ext.has("NewPlugin")).to_equal(true)
```

</details>

#### locked container uses resolve_or for missing plugins

1. ext lock
   - Expected: result equals `default-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
val result = ext.resolve_or("MissingPlugin", "default-plugin")
expect(result).to_equal("default-plugin")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
