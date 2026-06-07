# Extensions Phases Specification

> <details>

<!-- sdn-diagram:id=extensions_phases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=extensions_phases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

extensions_phases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=extensions_phases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extensions Phases Specification

## Scenarios

### Extensions: Phase 1 - Basic API

#### container construction

#### creates empty extensions container

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.has("Anything")).to_equal(false)
```

</details>

#### starts with no bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("Missing", nil)
expect(result).to_be_nil()
```

</details>

#### profile is set correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.profile).to_equal("dev")
```

</details>

#### locked is false by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.locked).to_equal(false)
```

</details>

#### bind_instance operations

#### registers a text value

1. ext bind instance
   - Expected: ext.has("MyPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("MyPlugin", "plugin-v1")
expect(ext.has("MyPlugin")).to_equal(true)
```

</details>

#### resolves a registered text value

1. ext bind instance
   - Expected: result equals `file-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("Logger", "file-logger")
val result = ext.resolve("Logger")
expect(result).to_equal("file-logger")
```

</details>

#### registers an integer value

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

#### registers a boolean value

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

#### resolve_or operations

#### returns nil for unregistered name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("NotHere", nil)
expect(result).to_be_nil()
```

</details>

#### returns default text for unregistered name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("NotHere", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### returns registered value when present

1. ext bind instance
   - Expected: result equals `profiler-v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("Profiler", "profiler-v2")
val result = ext.resolve_or("Profiler", "default")
expect(result).to_equal("profiler-v2")
```

</details>

#### has operations

#### has returns false for unregistered

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.has("X")).to_equal(false)
```

</details>

#### has returns true for registered

1. ext bind instance
   - Expected: ext.has("X") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("X", 1)
expect(ext.has("X")).to_equal(true)
```

</details>

### Extensions: Phase 2 - Integration

#### multiple plugins

#### registers two plugins independently

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
ext.bind_instance("PluginA", "a")
ext.bind_instance("PluginB", "b")
expect(ext.has("PluginA")).to_equal(true)
expect(ext.has("PluginB")).to_equal(true)
```

</details>

#### resolves two plugins independently

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

#### registering one plugin does not affect another

1. ext bind instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("PluginX", "x-value")
val other = ext.resolve_or("PluginY", nil)
expect(other).to_be_nil()
```

</details>

#### three plugins all registered correctly

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

#### factory-based binding

#### bind factory creates value on resolve

1. ext bind
   - Expected: ext.has("LazyPlugin") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind("LazyPlugin", fn(): "lazy-value")
expect(ext.has("LazyPlugin")).to_equal(true)
```

</details>

#### bind factory resolves to returned value

1. ext bind
   - Expected: result equals `created-on-demand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind("Created", fn(): "created-on-demand")
val result = ext.resolve("Created")
expect(result).to_equal("created-on-demand")
```

</details>

#### factory and instance bindings coexist

1. ext bind
2. ext bind instance
   - Expected: ext.resolve("Lazy") equals `lazy`
   - Expected: ext.resolve("Eager") equals `eager`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind("Lazy", fn(): "lazy")
ext.bind_instance("Eager", "eager")
expect(ext.resolve("Lazy")).to_equal("lazy")
expect(ext.resolve("Eager")).to_equal("eager")
```

</details>

#### extensions does not contain typed backend

#### backend is not in extensions by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("Backend", nil)
expect(result).to_be_nil()
```

</details>

#### extensions starts clean for plugin use

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.has("Backend")).to_equal(false)
expect(ext.has("Logger")).to_equal(false)
```

</details>

### Extensions: Phase 3 - System behavior

#### lock protects extensions

#### is_locked is false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
expect(ext.is_locked()).to_equal(false)
```

</details>

#### lock sets is_locked to true

1. ext lock
   - Expected: ext.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
expect(ext.is_locked()).to_equal(true)
```

</details>

#### locked container rejects bind_instance

1. ext lock
2. ext bind instance
   - Expected: ext.has("LockedPlugin") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
ext.bind_instance("LockedPlugin", "blocked")
expect(ext.has("LockedPlugin")).to_equal(false)
```

</details>

#### locked container rejects bind factory

1. ext lock
2. ext bind
   - Expected: ext.has("Blocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
ext.bind("Blocked", fn(): "never")
expect(ext.has("Blocked")).to_equal(false)
```

</details>

#### unlock allows registration again

1. ext lock
2. ext bind instance
   - Expected: ext.has("Pre") is false
3. ext unlock
4. ext bind instance
   - Expected: ext.has("Pre") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
ext.bind_instance("Pre", "v1")
expect(ext.has("Pre")).to_equal(false)
ext.unlock()
ext.bind_instance("Pre", "v1")
expect(ext.has("Pre")).to_equal(true)
```

</details>

#### pre-lock bindings still resolvable after lock

1. ext bind instance
2. ext lock
   - Expected: result equals `core-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.bind_instance("Core", "core-plugin")
ext.lock()
val result = ext.resolve("Core")
expect(result).to_equal("core-plugin")
```

</details>

#### resolve_or with defaults

#### locked container uses resolve_or for missing

1. ext lock
   - Expected: result equals `default-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
ext.lock()
val result = ext.resolve_or("Missing", "default-plugin")
expect(result).to_equal("default-plugin")
```

</details>

#### resolve_or returns nil default correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("NoPlugin", nil)
expect(result).to_be_nil()
```

</details>

#### edge cases

#### empty name resolves to default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_ext()
val result = ext.resolve_or("", "empty-default")
expect(result).to_equal("empty-default")
```

</details>

#### overwrite binding replaces old value

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/di/extensions_phases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Extensions: Phase 1 - Basic API
- Extensions: Phase 2 - Integration
- Extensions: Phase 3 - System behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
