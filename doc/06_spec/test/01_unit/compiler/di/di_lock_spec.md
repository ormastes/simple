# Di Lock Specification

> 1. di bind instance

<!-- sdn-diagram:id=di_lock_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_lock_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_lock_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_lock_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Lock Specification

## Scenarios

### DI Container Lock

### explicit lock

#### blocks bind when locked

1. di bind instance
   - Expected: di.has_binding("Foo") is true
2. di lock
3. di bind instance
   - Expected: di.has_binding("Bar") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Foo", 42)
expect(di.has_binding("Foo")).to_equal(true)

di.lock()
di.bind_instance("Bar", 99)
expect(di.has_binding("Bar")).to_equal(false)
```

</details>

#### blocks bind factory when locked

1. di lock
2. di bind
   - Expected: di.has_binding("Baz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind("Baz", fn(): 123)
expect(di.has_binding("Baz")).to_equal(false)
```

</details>

#### allows bind after unlock

1. di lock
2. di bind instance
   - Expected: di.has_binding("Foo") is false
3. di unlock
4. di bind instance
   - Expected: di.has_binding("Foo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind_instance("Foo", 42)
expect(di.has_binding("Foo")).to_equal(false)

di.unlock()
di.bind_instance("Foo", 42)
expect(di.has_binding("Foo")).to_equal(true)
```

</details>

#### is_locked returns true when locked

1. di lock
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
expect(di.is_locked()).to_equal(false)
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### resolve still works when locked

1. di bind instance
2. di lock
   - Expected: di.resolve("Svc") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Svc", "hello")
di.lock()
expect(di.resolve("Svc")).to_equal("hello")
```

</details>

### env-var based lock

#### env lock active when SIMPLE_SYSTEM_TEST=1

1. rt env set
2. rt env set
   - Expected: env_locked is true
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")

val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(true)

# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### env lock not active when SIMPLE_SYSTEM_TEST=0

1. rt env set
2. rt env set
   - Expected: env_locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")

val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(false)
```

</details>

#### env lock bypassed when SIMPLE_DI_TEST=1

1. rt env set
2. rt env set
   - Expected: env_locked is false
3. rt env set
4. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")

val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(false)

# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

#### env lock state changes with env vars

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is true
3. rt env set
   - Expected: di_is_system_test_locked() is false
4. rt env set
5. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")

expect(di_is_system_test_locked()).to_equal(true)

rt_env_set("SIMPLE_DI_TEST", "1")
expect(di_is_system_test_locked()).to_equal(false)

# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

### di_is_system_test_locked

#### returns false when no env var set

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "")
rt_env_set("SIMPLE_DI_TEST", "")
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### returns true when system test without di_test

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is true
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)

# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### returns false when di_test allows

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is false
3. rt env set
4. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")
expect(di_is_system_test_locked()).to_equal(false)

# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

### locked preserves existing bindings

#### pre-lock bindings remain resolvable

1. di bind instance
2. di bind instance
3. di lock
   - Expected: di.resolve("Backend") equals `production-backend`
   - Expected: di.resolve("Logger") equals `file-logger`
4. di bind instance
   - Expected: di.resolve("Backend") equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Backend", "production-backend")
di.bind_instance("Logger", "file-logger")
di.lock()

# Existing bindings work
expect(di.resolve("Backend")).to_equal("production-backend")
expect(di.resolve("Logger")).to_equal("file-logger")

# New bindings rejected
di.bind_instance("Backend", "mock-backend")
expect(di.resolve("Backend")).to_equal("production-backend")
```

</details>

#### resolve_or works when locked

1. di bind instance
2. di lock
   - Expected: di.resolve_or("Config", "default") equals `prod-config`
   - Expected: di.resolve_or("Missing", "fallback") equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Config", "prod-config")
di.lock()

expect(di.resolve_or("Config", "default")).to_equal("prod-config")
expect(di.resolve_or("Missing", "fallback")).to_equal("fallback")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/di/di_lock_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DI Container Lock
- explicit lock
- env-var based lock
- di_is_system_test_locked
- locked preserves existing bindings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
