# Di Lock Phases Specification

> <details>

<!-- sdn-diagram:id=di_lock_phases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_lock_phases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_lock_phases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_lock_phases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Lock Phases Specification

## Scenarios

### DiLock: Phase 1 - Basic API

#### initial state

#### container is unlocked by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
expect(di.is_locked()).to_equal(false)
```

</details>

#### locked field is false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
expect(di.locked).to_equal(false)
```

</details>

#### bind_instance works when unlocked

1. di bind instance
   - Expected: di.has_binding("Service") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Service", "value")
expect(di.has_binding("Service")).to_equal(true)
```

</details>

#### lock operations

#### lock sets is_locked to true

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

#### lock prevents bind_instance

1. di lock
2. di bind instance
   - Expected: di.has_binding("Blocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_instance("Blocked", "value")
expect(di.has_binding("Blocked")).to_equal(false)
```

</details>

#### lock prevents bind factory

1. di lock
2. di bind
   - Expected: di.has_binding("BlockedFn") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind("BlockedFn", fn(): "value")
expect(di.has_binding("BlockedFn")).to_equal(false)
```

</details>

#### lock does not clear existing bindings

1. di bind instance
2. di lock
   - Expected: di.has_binding("PreLock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("PreLock", "early")
di.lock()
expect(di.has_binding("PreLock")).to_equal(true)
```

</details>

#### unlock operations

#### unlock sets is_locked to false

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

#### unlock allows bind_instance again

1. di lock
2. di unlock
3. di bind instance
   - Expected: di.has_binding("AfterUnlock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.unlock()
di.bind_instance("AfterUnlock", "allowed")
expect(di.has_binding("AfterUnlock")).to_equal(true)
```

</details>

#### unlock allows bind factory again

1. di lock
2. di unlock
3. di bind
   - Expected: di.has_binding("FactoryAfter") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.unlock()
di.bind("FactoryAfter", fn(): "factory-value")
expect(di.has_binding("FactoryAfter")).to_equal(true)
```

</details>

#### resolve while locked

#### resolve works on pre-lock bindings

1. di bind instance
2. di lock
   - Expected: di.resolve("Config") equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Config", "prod-config")
di.lock()
expect(di.resolve("Config")).to_equal("prod-config")
```

</details>

#### resolve_or works while locked

1. di bind instance
2. di lock
   - Expected: di.resolve_or("Setting", "off") equals `on`
   - Expected: di.resolve_or("Missing", "default") equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Setting", "on")
di.lock()
expect(di.resolve_or("Setting", "off")).to_equal("on")
expect(di.resolve_or("Missing", "default")).to_equal("default")
```

</details>

### DiLock: Phase 2 - Integration

#### lock protects production bindings

#### pre-lock backend binding is protected

1. di bind instance
2. di lock
3. di bind instance
   - Expected: di.resolve("Backend") equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.lock()
di.bind_instance("Backend", "mock-backend")
expect(di.resolve("Backend")).to_equal("production-backend")
```

</details>

#### two pre-lock bindings both resolvable after lock

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

#### lock-unlock-relock cycle works

1. di bind instance
2. di lock
   - Expected: di.has_binding("A") is true
3. di unlock
4. di bind instance
5. di lock
   - Expected: di.has_binding("A") is true
   - Expected: di.has_binding("B") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("A", "first")
di.lock()
expect(di.has_binding("A")).to_equal(true)
di.unlock()
di.bind_instance("B", "second")
di.lock()
expect(di.has_binding("A")).to_equal(true)
expect(di.has_binding("B")).to_equal(true)
```

</details>

#### di_is_system_test_locked function

#### returns false when SIMPLE_SYSTEM_TEST is not 1

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is false
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(false)
rt_env_set("SIMPLE_SYSTEM_TEST", "")
```

</details>

#### returns true when SIMPLE_SYSTEM_TEST=1 and no di_test

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is true
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### returns false when SIMPLE_DI_TEST=1 bypasses lock

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is false
3. rt env set
4. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")
expect(di_is_system_test_locked()).to_equal(false)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

#### env-var based locking

#### env lock active when SIMPLE_SYSTEM_TEST=1

1. rt env set
2. rt env set
   - Expected: env_locked is true
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### env lock not active when SIMPLE_DI_TEST=1

1. rt env set
2. rt env set
   - Expected: env_locked is false
3. rt env set
4. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(false)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

#### no env lock when SIMPLE_SYSTEM_TEST=0

1. rt env set
   - Expected: env_locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(false)
```

</details>

### DiLock: Phase 3 - System behavior

#### lock as system test guard

#### locked container is_locked reflects explicit lock

1. di lock
   - Expected: di.is_locked() is true
2. di unlock
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
expect(di.is_locked()).to_equal(false)
di.lock()
expect(di.is_locked()).to_equal(true)
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### locked container blocks bind_tagged

1. di lock
2. di bind tagged
   - Expected: di.has_binding("TaggedSvc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_tagged("TaggedSvc", ["system"], fn(): "tagged-val")
expect(di.has_binding("TaggedSvc")).to_equal(false)
```

</details>

#### has returns false for bindings rejected by lock

1. di lock
2. di bind instance
   - Expected: di.has_binding("NotRegistered") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_instance("NotRegistered", "value")
expect(di.has_binding("NotRegistered")).to_equal(false)
```

</details>

#### lock preserves resolve_or semantics

#### resolve_or returns pre-lock value when locked

1. di bind instance
2. di lock
   - Expected: result equals `registered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Svc", "registered")
di.lock()
val result = di.resolve_or("Svc", "default")
expect(result).to_equal("registered")
```

</details>

#### resolve_or returns default for missing when locked

1. di lock
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
val result = di.resolve_or("Absent", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### env-var cleanup

#### env lock only active when SIMPLE_SYSTEM_TEST=1

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

#### env lock active then cleared works

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is true
3. rt env set
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### di_test bypass only works when system_test is also 1

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is false
3. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "1")
expect(di_is_system_test_locked()).to_equal(false)
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/di/di_lock_phases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DiLock: Phase 1 - Basic API
- DiLock: Phase 2 - Integration
- DiLock: Phase 3 - System behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
