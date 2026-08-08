# DI Lock Feature

> Tests the DiContainer lock/unlock mechanism across all phases: lock state transitions, locked behavior that rejects new bindings while allowing resolution, lock semantics including pre-lock binding preservation and overwrite protection, integration with environment variable locking, and a complete system test covering the full registration-lock-resolve-unlock-extend lifecycle.

<!-- sdn-diagram:id=di_lock_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_lock_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_lock_feature_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_lock_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DI Lock Feature

Tests the DiContainer lock/unlock mechanism across all phases: lock state transitions, locked behavior that rejects new bindings while allowing resolution, lock semantics including pre-lock binding preservation and overwrite protection, integration with environment variable locking, and a complete system test covering the full registration-lock-resolve-unlock-extend lifecycle.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DI-004 |
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/feature/usage/di_lock_feature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the DiContainer lock/unlock mechanism across all phases: lock state
transitions, locked behavior that rejects new bindings while allowing resolution,
lock semantics including pre-lock binding preservation and overwrite protection,
integration with environment variable locking, and a complete system test
covering the full registration-lock-resolve-unlock-extend lifecycle.

## Syntax

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Backend", "production-backend")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
```
DI Lock Feature Spec

Feature 9: DI Lock

DiContainer with lock()/unlock() — once locked, no new bindings can be added.
Covers all phases: lock state, locked behavior, lock semantics, integration,
and full system test.

## Scenarios

### DI Lock Feature: Phase 1 - Lock state

#### starts unlocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
expect(di.locked).to_equal(false)
```

</details>

#### lock() transitions to locked state

1. di lock
   - Expected: di.locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
expect(di.locked).to_equal(true)
```

</details>

#### is_locked() returns true after lock

1. di lock
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### unlock() transitions back to unlocked

1. di lock
2. di unlock
   - Expected: di.locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.unlock()
expect(di.locked).to_equal(false)
```

</details>

#### is_locked() returns false after unlock

1. di lock
2. di unlock
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### is_locked() returns false on fresh container

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
expect(di.is_locked()).to_equal(false)
```

</details>

### DI Lock Feature: Phase 2 - Locked behavior

#### locked container rejects bind_instance

1. di lock
2. di bind instance
   - Expected: di.has_binding("Bar") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_instance("Bar", 99)
expect(di.has_binding("Bar")).to_equal(false)
```

</details>

#### locked container rejects bind

1. di lock
2. di bind
   - Expected: di.has_binding("Baz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind("Baz", fn(): 123)
expect(di.has_binding("Baz")).to_equal(false)
```

</details>

#### locked container still allows resolve

1. di bind instance
2. di lock
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Svc", "hello")
di.lock()
val result = di.resolve("Svc")
expect(result).to_equal("hello")
```

</details>

#### locked container still allows resolve_or

1. di bind instance
2. di lock
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Svc", "hello")
di.lock()
val result = di.resolve_or("Svc", "default")
expect(result).to_equal("hello")
```

</details>

#### locked container still allows has check

1. di bind instance
2. di lock
   - Expected: di.has_binding("Svc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Svc", "hello")
di.lock()
expect(di.has_binding("Svc")).to_equal(true)
```

</details>

#### locked container resolve_or returns default for missing

1. di lock
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
val result = di.resolve_or("Missing", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### locked container rejects bind_tagged

1. di lock
2. di bind tagged
   - Expected: di.has_binding("Tagged") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_tagged("Tagged", ["api"], fn(): "tagged-val")
expect(di.has_binding("Tagged")).to_equal(false)
```

</details>

### DI Lock Feature: Phase 3 - Lock semantics

#### can lock and unlock multiple times

1. di lock
   - Expected: di.is_locked() is true
2. di unlock
   - Expected: di.is_locked() is false
3. di lock
   - Expected: di.is_locked() is true
4. di unlock
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
expect(di.is_locked()).to_equal(true)
di.unlock()
expect(di.is_locked()).to_equal(false)
di.lock()
expect(di.is_locked()).to_equal(true)
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### bindings before lock are preserved after lock

1. di bind instance
2. di bind instance
3. di lock
   - Expected: di.resolve("Backend") equals `production-backend`
   - Expected: di.resolve("Logger") equals `file-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.bind_instance("Logger", "file-logger")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
expect(di.resolve("Logger")).to_equal("file-logger")
```

</details>

#### unlock allows new bindings again

1. di lock
2. di bind instance
   - Expected: di.has_binding("Foo") is false
3. di unlock
4. di bind instance
   - Expected: di.has_binding("Foo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_instance("Foo", 42)
expect(di.has_binding("Foo")).to_equal(false)
di.unlock()
di.bind_instance("Foo", 42)
expect(di.has_binding("Foo")).to_equal(true)
```

</details>

#### pre-lock binding not overwritten when locked

1. di bind instance
2. di lock
3. di bind instance
   - Expected: result equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.lock()
di.bind_instance("Backend", "mock-backend")
val result = di.resolve("Backend")
expect(result).to_equal("production-backend")
```

</details>

#### locked state does not affect resolve_or nil default

1. di lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
val result = di.resolve_or("NoSuch", nil)
expect(result).to_be_nil()
```

</details>

### DI Lock Feature: Phase 4 - Integration

#### container locked after setup phase

1. di bind instance
2. di bind instance
3. di lock
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
# Setup phase: register services
di.bind_instance("Service1", "svc1")
di.bind_instance("Service2", "svc2")
# Lock to prevent further modification
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### runtime resolution works on locked container

1. di bind instance
2. di lock
   - Expected: result equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Config", "prod-config")
di.lock()
val result = di.resolve("Config")
expect(result).to_equal("prod-config")
```

</details>

#### locked container with resolve_singleton works

1. di bind
2. di lock
   - Expected: result equals `singleton-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind("Singleton", fn(): "singleton-value")
di.lock()
val result = di.resolve("Singleton")
expect(result).to_equal("singleton-value")
```

</details>

#### multiple services still resolvable after lock

1. di bind instance
2. di bind instance
3. di bind instance
4. di lock
   - Expected: di.resolve("A") equals `alpha`
   - Expected: di.resolve("B") equals `beta`
   - Expected: di.resolve("C") equals `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("A", "alpha")
di.bind_instance("B", "beta")
di.bind_instance("C", "gamma")
di.lock()
expect(di.resolve("A")).to_equal("alpha")
expect(di.resolve("B")).to_equal("beta")
expect(di.resolve("C")).to_equal("gamma")
```

</details>

#### env-var lock is active when system test active

1. rt env set
2. rt env set
   - Expected: env_locked is true
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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

#### env-var di_test bypass disables env lock

1. rt env set
2. rt env set
   - Expected: env_locked is false
3. rt env set
4. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
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

### DI Lock Feature: Phase 5 - System test

#### full registration-lock-resolve cycle works

1. di bind instance
2. di bind instance
3. di lock
   - Expected: di.is_locked() is true
   - Expected: di.resolve("key1") equals `val1`
   - Expected: di.resolve("key2") equals `val2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("key1", "val1")
di.bind_instance("key2", "val2")
di.lock()
expect(di.is_locked()).to_equal(true)
expect(di.resolve("key1")).to_equal("val1")
expect(di.resolve("key2")).to_equal("val2")
```

</details>

#### complete lifecycle: register, lock, reject, unlock, register again

1. di bind instance
2. di lock
   - Expected: di.is_locked() is true
3. di bind instance
   - Expected: di.has_binding("Extra") is false
   - Expected: di.resolve("Core") equals `core-impl`
4. di unlock
5. di bind instance
   - Expected: di.has_binding("Extra") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
# Phase 1: register core bindings
di.bind_instance("Core", "core-impl")
# Phase 2: lock the container
di.lock()
expect(di.is_locked()).to_equal(true)
# Phase 3: locked — new bindings rejected
di.bind_instance("Extra", "extra-impl")
expect(di.has_binding("Extra")).to_equal(false)
# Phase 4: core bindings still work
expect(di.resolve("Core")).to_equal("core-impl")
# Phase 5: unlock — new bindings accepted
di.unlock()
di.bind_instance("Extra", "extra-impl")
expect(di.has_binding("Extra")).to_equal(true)
```

</details>

#### factory bindings registered before lock resolve correctly

1. di bind
2. di lock
   - Expected: result equals `created-on-demand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind("LazyService", fn(): "created-on-demand")
di.lock()
val result = di.resolve("LazyService")
expect(result).to_equal("created-on-demand")
```

</details>

#### di_is_system_test_locked returns false with no env vars

1. rt env set
2. rt env set
   - Expected: locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "")
rt_env_set("SIMPLE_DI_TEST", "")
val locked = di_is_system_test_locked()
expect(locked).to_equal(false)
```

</details>

#### di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1

1. rt env set
2. rt env set
   - Expected: locked is true
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
val locked = di_is_system_test_locked()
expect(locked).to_equal(true)
# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
