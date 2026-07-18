# DI System Test Lock - All Phases

> Comprehensive phase tests for the DI system test lock feature covering all five phases: lock state transitions (lock/unlock/cycle), binding rejection when locked (bind_instance, bind, bind_tagged), resolution behavior while locked (resolve, resolve_or, has), lock integration with registration protection, and full DI lifecycle including environment variable lock with SIMPLE_DI_TEST bypass.

<!-- sdn-diagram:id=di_lock_all_phases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_lock_all_phases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_lock_all_phases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_lock_all_phases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DI System Test Lock - All Phases

Comprehensive phase tests for the DI system test lock feature covering all five phases: lock state transitions (lock/unlock/cycle), binding rejection when locked (bind_instance, bind, bind_tagged), resolution behavior while locked (resolve, resolve_or, has), lock integration with registration protection, and full DI lifecycle including environment variable lock with SIMPLE_DI_TEST bypass.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DI-003 |
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/feature/usage/di_lock_all_phases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive phase tests for the DI system test lock feature covering all five
phases: lock state transitions (lock/unlock/cycle), binding rejection when locked
(bind_instance, bind, bind_tagged), resolution behavior while locked (resolve,
resolve_or, has), lock integration with registration protection, and full DI
lifecycle including environment variable lock with SIMPLE_DI_TEST bypass.

## Syntax

```simple
val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind_instance("key", "value")  # silently rejected
expect(di.resolve_or("key", "fallback")).to_equal("fallback")
```
DI Lock All Phases Spec

Comprehensive phase tests for Feature 9: DI System Test Lock.
Covers all 5 phases of the DI lock feature lifecycle.

Feature: DI System Test Lock (Feature 9)
Source: src/compiler/di.spl

DiContainer has:
  lock()           - explicitly lock (prevents all bind operations)
  unlock()         - explicitly unlock (does NOT override env-var lock)
  is_locked()      - true if locked field OR env-var lock is active
  bind_instance()  - bind a pre-created instance (rejected when locked)
  bind()           - bind a factory fn (rejected when locked)
  bind_for_profile() - bind factory for a specific profile (rejected when locked)
  bind_tagged()    - bind with tags (rejected when locked)
  resolve()        - resolve binding by name (always works)
  resolve_or()     - resolve with default fallback (always works)
  has()            - check if binding exists (always works)

## Scenarios

### DI Lock: Phase 1 - Lock state transitions

#### initial state

#### new container is unlocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
expect(di.is_locked()).to_equal(false)
```

</details>

#### locked field is false on construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
expect(di.locked).to_equal(false)
```

</details>

#### binding works before any lock

1. di bind instance
   - Expected: di.has_binding("Svc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Svc", "value")
expect(di.has_binding("Svc")).to_equal(true)
```

</details>

#### lock transitions

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

#### unlock after lock sets is_locked to false

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

#### multiple lock calls remain locked

1. di lock
2. di lock
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### unlock without prior lock stays unlocked

1. di unlock
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### lock-unlock-lock cycle ends locked

1. di lock
2. di unlock
3. di lock
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.unlock()
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

### DI Lock: Phase 2 - Binding behavior when locked

#### bind_instance is blocked

#### bind_instance rejected when locked

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

#### bind_instance succeeds before lock

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

#### bind factory is blocked

#### bind factory rejected when locked

1. di lock
2. di bind
   - Expected: di.has_binding("FactoryBlocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind("FactoryBlocked", fn(): "factory-val")
expect(di.has_binding("FactoryBlocked")).to_equal(false)
```

</details>

#### bind_tagged rejected when locked

1. di lock
2. di bind tagged
   - Expected: di.has_binding("TaggedBlocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_tagged("TaggedBlocked", ["system"], fn(): "tagged-val")
expect(di.has_binding("TaggedBlocked")).to_equal(false)
```

</details>

#### bind allowed after unlock

#### bind_instance works after unlock

1. di lock
2. di bind instance
   - Expected: di.has_binding("Blocked") is false
3. di unlock
4. di bind instance
   - Expected: di.has_binding("Allowed") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_instance("Blocked", "value")
expect(di.has_binding("Blocked")).to_equal(false)
di.unlock()
di.bind_instance("Allowed", "unlocked-value")
expect(di.has_binding("Allowed")).to_equal(true)
```

</details>

#### bind factory works after unlock

1. di lock
2. di unlock
3. di bind
   - Expected: di.has_binding("FactoryAfterUnlock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.unlock()
di.bind("FactoryAfterUnlock", fn(): "recovered")
expect(di.has_binding("FactoryAfterUnlock")).to_equal(true)
```

</details>

### DI Lock: Phase 3 - Resolution behavior

#### resolve works while locked

#### resolve pre-lock singleton works

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

#### resolve pre-lock factory works

1. di bind
2. di lock
   - Expected: di.resolve("Builder") equals `built-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind("Builder", fn(): "built-value")
di.lock()
expect(di.resolve("Builder")).to_equal("built-value")
```

</details>

#### resolve_or works while locked

#### resolve_or returns registered value when locked

1. di bind instance
2. di lock
   - Expected: di.resolve_or("Setting", "off") equals `on`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Setting", "on")
di.lock()
expect(di.resolve_or("Setting", "off")).to_equal("on")
```

</details>

#### resolve_or returns default for missing when locked

1. di lock
   - Expected: di.resolve_or("Missing", "fallback") equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
expect(di.resolve_or("Missing", "fallback")).to_equal("fallback")
```

</details>

#### has works correctly

#### has returns true for pre-lock binding

1. di bind instance
2. di lock
   - Expected: di.has_binding("Present") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Present", "here")
di.lock()
expect(di.has_binding("Present")).to_equal(true)
```

</details>

#### has returns false for post-lock rejected binding

1. di lock
2. di bind instance
   - Expected: di.has_binding("Rejected") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.lock()
di.bind_instance("Rejected", "nope")
expect(di.has_binding("Rejected")).to_equal(false)
```

</details>

### DI Lock: Phase 4 - Lock integration with registration

#### protects production bindings

#### pre-lock binding cannot be overwritten while locked

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

#### multiple pre-lock bindings all resolvable after lock

1. di bind instance
2. di bind instance
3. di bind instance
4. di lock
   - Expected: di.resolve("Backend") equals `production-backend`
   - Expected: di.resolve("Logger") equals `file-logger`
   - Expected: di.resolve("Config") equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.bind_instance("Logger", "file-logger")
di.bind_instance("Config", "prod-config")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
expect(di.resolve("Logger")).to_equal("file-logger")
expect(di.resolve("Config")).to_equal("prod-config")
```

</details>

#### extend after unlock

#### new bindings added after unlock are accessible

1. di bind instance
2. di lock
3. di unlock
4. di bind instance
   - Expected: di.has_binding("First") is true
   - Expected: di.has_binding("Second") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("First", "value-a")
di.lock()
di.unlock()
di.bind_instance("Second", "value-b")
expect(di.has_binding("First")).to_equal(true)
expect(di.has_binding("Second")).to_equal(true)
```

</details>

#### lock-unlock-relock preserves all accumulated bindings

1. di bind instance
2. di lock
3. di unlock
4. di bind instance
5. di lock
   - Expected: di.resolve("A") equals `first`
   - Expected: di.resolve("B") equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("A", "first")
di.lock()
di.unlock()
di.bind_instance("B", "second")
di.lock()
expect(di.resolve("A")).to_equal("first")
expect(di.resolve("B")).to_equal("second")
```

</details>

#### env-var lock mechanism

#### di_is_system_test_locked returns false normally

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

#### env lock is active when system test active

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

### DI Lock: Phase 5 - System full DI lifecycle

#### complete register-lock-resolve cycle

#### full DI lifecycle: register, lock, resolve, unlock, extend

1. di bind instance
2. di bind instance
3. di bind
4. di lock
   - Expected: di.is_locked() is true
   - Expected: di.resolve("logger") equals `console_logger`
   - Expected: di.resolve("config") equals `prod_config`
   - Expected: di.resolve("parser") equals `default_parser`
5. di bind instance
   - Expected: di.has_binding("extra") is false
6. di unlock
   - Expected: di.is_locked() is false
7. di bind instance
   - Expected: di.resolve("extra") equals `new_service`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
# Phase A: Register services
di.bind_instance("logger", "console_logger")
di.bind_instance("config", "prod_config")
di.bind("parser", fn(): "default_parser")
# Phase B: Lock for production use
di.lock()
expect(di.is_locked()).to_equal(true)
# Phase C: Resolve (should work)
expect(di.resolve("logger")).to_equal("console_logger")
expect(di.resolve("config")).to_equal("prod_config")
expect(di.resolve("parser")).to_equal("default_parser")
# Phase D: Reject new bindings
di.bind_instance("extra", "injected")
expect(di.has_binding("extra")).to_equal(false)
# Phase E: Unlock and extend
di.unlock()
expect(di.is_locked()).to_equal(false)
di.bind_instance("extra", "new_service")
expect(di.resolve("extra")).to_equal("new_service")
```

</details>

#### resolve_or covers missing services during operation

1. di bind instance
2. di lock
   - Expected: logger equals `syslog`
   - Expected: tracer equals `noop_tracer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("logger", "syslog")
di.lock()
val logger = di.resolve_or("logger", "noop_logger")
val tracer = di.resolve_or("tracer", "noop_tracer")
expect(logger).to_equal("syslog")
expect(tracer).to_equal("noop_tracer")
```

</details>

#### has correctly reflects what is and is not registered

1. di bind instance
2. di bind
3. di lock
4. di bind instance
   - Expected: di.has_binding("ServiceA") is true
   - Expected: di.has_binding("ServiceB") is true
   - Expected: di.has_binding("ServiceC") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = make_di()
di.bind_instance("ServiceA", "a")
di.bind("ServiceB", fn(): "b")
di.lock()
# Post-lock: ServiceC rejected
di.bind_instance("ServiceC", "c")
expect(di.has_binding("ServiceA")).to_equal(true)
expect(di.has_binding("ServiceB")).to_equal(true)
expect(di.has_binding("ServiceC")).to_equal(false)
```

</details>

#### env-var lock full flow

#### env lock reflects env state then resets

1. rt env set
2. rt env set
   - Expected: di_is_system_test_locked() is true
3. rt env set
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
# After clearing env, env lock is off
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### SIMPLE_DI_TEST=1 bypass disables env lock

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
