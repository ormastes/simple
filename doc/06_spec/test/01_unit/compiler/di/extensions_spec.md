# Extensions Specification

> 1. ext bind instance

<!-- sdn-diagram:id=extensions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=extensions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

extensions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=extensions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extensions Specification

## Scenarios

### Extensions container: plugin registration

#### registers a plugin by name

1. ext bind instance
   - Expected: ext.has("Profiler") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.bind_instance("Profiler", "profiler-v1")
expect(ext.has("Profiler")).to_equal(true)
```

</details>

#### resolves a registered plugin

1. ext bind instance
   - Expected: result equals `fmt-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.bind_instance("Formatter", "fmt-plugin")
val result = ext.resolve("Formatter")
expect(result).to_equal("fmt-plugin")
```

</details>

#### returns nil for unregistered plugin via resolve_or

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
val result = ext.resolve_or("MissingPlugin", nil)
expect(result).to_be_nil()
```

</details>

#### returns default for unregistered plugin via resolve_or

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
val result = ext.resolve_or("MissingPlugin", "default-value")
expect(result).to_equal("default-value")
```

</details>

#### registers multiple plugins independently

1. ext bind instance
2. ext bind instance
   - Expected: ext.has("PluginA") is true
   - Expected: ext.has("PluginB") is true
   - Expected: ext.resolve("PluginA") equals `a`
   - Expected: ext.resolve("PluginB") equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.bind_instance("PluginA", "a")
ext.bind_instance("PluginB", "b")
expect(ext.has("PluginA")).to_equal(true)
expect(ext.has("PluginB")).to_equal(true)
expect(ext.resolve("PluginA")).to_equal("a")
expect(ext.resolve("PluginB")).to_equal("b")
```

</details>

#### registers numeric plugin values

1. ext bind instance
   - Expected: result equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.bind_instance("MaxWorkers", 4)
val result = ext.resolve("MaxWorkers")
expect(result).to_equal(4)
```

</details>

### Extensions container: lock behavior

#### blocks registration when locked

1. ext lock
2. ext bind instance
   - Expected: ext.has("LockedPlugin") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.lock()
ext.bind_instance("LockedPlugin", "should-not-register")
expect(ext.has("LockedPlugin")).to_equal(false)
```

</details>

#### allows registration after unlock

1. ext lock
2. ext bind instance
   - Expected: ext.has("Temp") is false
3. ext unlock
4. ext bind instance
   - Expected: ext.has("Temp") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.lock()
ext.bind_instance("Temp", "v1")
expect(ext.has("Temp")).to_equal(false)

ext.unlock()
ext.bind_instance("Temp", "v1")
expect(ext.has("Temp")).to_equal(true)
```

</details>

#### resolve still works when locked

1. ext bind instance
2. ext lock
   - Expected: result equals `log-plugin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.bind_instance("Logger", "log-plugin")
ext.lock()
val result = ext.resolve("Logger")
expect(result).to_equal("log-plugin")
```

</details>

#### is_locked reflects lock state

1. ext lock
   - Expected: ext.is_locked() is true
2. ext unlock
   - Expected: ext.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
expect(ext.is_locked()).to_equal(false)
ext.lock()
expect(ext.is_locked()).to_equal(true)
ext.unlock()
expect(ext.is_locked()).to_equal(false)
```

</details>

### Extensions container: separation of concerns

#### extensions container starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
expect(ext.has("Backend")).to_equal(false)
expect(ext.has("Logger")).to_equal(false)
expect(ext.has("AnyPlugin")).to_equal(false)
```

</details>

#### typed backend field is separate from extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify extensions does NOT hold the backend (typed field does)
val ext = make_extensions()
val backend_in_ext = ext.resolve_or("Backend", nil)
expect(backend_in_ext).to_be_nil()
```

</details>

#### plugin registration does not affect other plugins

1. ext bind instance
   - Expected: x_val equals `x-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = make_extensions()
ext.bind_instance("PluginX", "x-value")
val other = ext.resolve_or("PluginY", nil)
expect(other).to_be_nil()
val x_val = ext.resolve("PluginX")
expect(x_val).to_equal("x-value")
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
val ext = make_extensions()
ext.bind("LazyPlugin", fn(): "lazy-created")
expect(ext.has("LazyPlugin")).to_equal(true)
val result = ext.resolve("LazyPlugin")
expect(result).to_equal("lazy-created")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/di/extensions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Extensions container: plugin registration
- Extensions container: lock behavior
- Extensions container: separation of concerns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
