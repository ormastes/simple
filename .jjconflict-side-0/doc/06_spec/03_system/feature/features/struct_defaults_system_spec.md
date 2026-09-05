# Struct Defaults System Specification

> <details>

<!-- sdn-diagram:id=struct_defaults_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=struct_defaults_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

struct_defaults_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=struct_defaults_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Defaults System Specification

## Scenarios

### Struct Defaults: Phase 1 - Parser supports default syntax

#### struct with integer default parses

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct TestConfig:
    timeout: i64 = 30
    retries: i64 = 3
val cfg = TestConfig()
expect(cfg.timeout).to_equal(30)
expect(cfg.retries).to_equal(3)
```

</details>

#### struct with text default works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Named:
    name: text = "unnamed"
val n = Named()
expect(n.name).to_equal("unnamed")
```

</details>

#### struct with bool default works

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Flags:
    enabled: bool = true
    debug: bool = false
val f = Flags()
expect(f.enabled).to_equal(true)
expect(f.debug).to_equal(false)
```

</details>

#### struct with float default works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Scale:
    factor: f64 = 1.0
val s = Scale()
expect(s.factor).to_equal(1.0)
```

</details>

#### can override specific defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Config:
    mode: text = "debug"
    verbose: bool = false
val c = Config(mode: "release")
expect(c.mode).to_equal("release")
expect(c.verbose).to_equal(false)
```

</details>

#### explicit value overrides default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64 = 0
    y: i64 = 0
val p = Point(x: 10, y: 20)
expect(p.x).to_equal(10)
expect(p.y).to_equal(20)
```

</details>

#### backward compatible - struct without defaults still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct NoDefaults:
    x: i64
    y: i64
val p = NoDefaults(x: 1, y: 2)
expect(p.x).to_equal(1)
expect(p.y).to_equal(2)
```

</details>

### Struct Defaults: Phase 2 - Integration

#### struct with arithmetic expression default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Buffer:
    capacity: i64 = 4 * 1024
val b = Buffer()
expect(b.capacity).to_equal(4096)
```

</details>

#### struct mixing fields with and without defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Node:
    id: i64
    count: i64 = 0
val n = Node(id: 5)
expect(n.id).to_equal(5)
expect(n.count).to_equal(0)
```

</details>

#### struct with array default field works

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Collection:
    items: [text] = []
    name: text = "default"
val c = Collection()
expect(c.name).to_equal("default")
```

</details>

#### nested struct definitions each with own defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Inner:
    value: i64 = 42
struct Outer:
    label: text = "outer"
val o = Outer()
expect(o.label).to_equal("outer")
```

</details>

#### multiple structs each with defaults in same scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct A:
    x: i64 = 1
struct B:
    y: i64 = 2
val a = A()
val b = B()
expect(a.x).to_equal(1)
expect(b.y).to_equal(2)
```

</details>

#### only partially provided fields use defaults for the rest

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct ThreeField:
    a: i64 = 10
    b: i64 = 20
    c: i64 = 30
val t = ThreeField(b: 99)
expect(t.a).to_equal(10)
expect(t.b).to_equal(99)
expect(t.c).to_equal(30)
```

</details>

### Struct Defaults: Phase 3 - System integration

#### compiler options struct with all defaults is usable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct CompilerConfig:
    mode: text = "interpret"
    verbose: bool = false
    output: text = "out"
val default_config = CompilerConfig()
expect(default_config.mode).to_equal("interpret")
expect(default_config.verbose).to_equal(false)
expect(default_config.output).to_equal("out")
```

</details>

#### can partially override compiler config defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct BuildConfig:
    target: text = "debug"
    optimize: bool = false
    warnings: bool = true
val release = BuildConfig(target: "release", optimize: true)
expect(release.target).to_equal("release")
expect(release.optimize).to_equal(true)
expect(release.warnings).to_equal(true)
```

</details>

#### struct defaults work correctly in function return

1. fn make default result
2. Result
   - Expected: r.ok is true
   - Expected: r.code equals `0`
   - Expected: r.msg equals `success`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Result:
    ok: bool = true
    code: i64 = 0
    msg: text = "success"

fn make_default_result() -> Result:
    Result()

val r = make_default_result()
expect(r.ok).to_equal(true)
expect(r.code).to_equal(0)
expect(r.msg).to_equal("success")
```

</details>

#### struct with defaults can be stored in variable and accessed

1. var settings = Settings
   - Expected: settings.max_retries equals `3`
   - Expected: settings.timeout_ms equals `5000`
   - Expected: settings.log_level equals `info`
   - Expected: custom.max_retries equals `10`
   - Expected: custom.timeout_ms equals `5000`
   - Expected: custom.log_level equals `debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Settings:
    max_retries: i64 = 3
    timeout_ms: i64 = 5000
    log_level: text = "info"

var settings = Settings()
expect(settings.max_retries).to_equal(3)
expect(settings.timeout_ms).to_equal(5000)
expect(settings.log_level).to_equal("info")

val custom = Settings(max_retries: 10, log_level: "debug")
expect(custom.max_retries).to_equal(10)
expect(custom.timeout_ms).to_equal(5000)
expect(custom.log_level).to_equal("debug")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/struct_defaults_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Struct Defaults: Phase 1 - Parser supports default syntax
- Struct Defaults: Phase 2 - Integration
- Struct Defaults: Phase 3 - System integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
