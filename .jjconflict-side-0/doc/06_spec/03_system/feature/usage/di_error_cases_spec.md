# DI Error Cases

> Tests the failure paths and edge cases of the DiContainer dependency injection system. Covers locked container behavior (binding rejection), missing key fallback via resolve_or, edge cases like empty keys and key overwrites, resolve behavior through locks, and environment variable-based system test locking via SIMPLE_SYSTEM_TEST/SIMPLE_DI_TEST.

<!-- sdn-diagram:id=di_error_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=di_error_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

di_error_cases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=di_error_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DI Error Cases

Tests the failure paths and edge cases of the DiContainer dependency injection system. Covers locked container behavior (binding rejection), missing key fallback via resolve_or, edge cases like empty keys and key overwrites, resolve behavior through locks, and environment variable-based system test locking via SIMPLE_SYSTEM_TEST/SIMPLE_DI_TEST.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/usage/di_error_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the failure paths and edge cases of the DiContainer dependency injection system.
Covers locked container behavior (binding rejection), missing key fallback via resolve_or,
edge cases like empty keys and key overwrites, resolve behavior through locks, and
environment variable-based system test locking via SIMPLE_SYSTEM_TEST/SIMPLE_DI_TEST.

## Scenarios

### DI Error Cases: locked container rejects bindings

#### bind_instance on locked container does not store value

1. di bind instance
2. di lock
3. di bind instance
   - Expected: di.has_binding("new_key") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("existing", "before")
di.lock()
di.bind_instance("new_key", "should_not_appear")
expect(di.has_binding("new_key")).to_equal(false)
```

</details>

#### bind factory on locked container does not register

1. di lock
2. di bind
   - Expected: di.has_binding("FactoryKey") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind("FactoryKey", fn(): "factory_result")
expect(di.has_binding("FactoryKey")).to_equal(false)
```

</details>

#### bind_for_profile on locked container does not register

1. di lock
2. di bind for profile
   - Expected: di.has_binding("ProfileKey") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind_for_profile("ProfileKey", CompilerProfile.Dev, fn(): "profiled")
expect(di.has_binding("ProfileKey")).to_equal(false)
```

</details>

#### locked container does not overwrite previously bound value

1. di bind instance
2. di lock
3. di bind instance
   - Expected: di.resolve("Service") equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Service", "original")
di.lock()
di.bind_instance("Service", "overwrite_attempt")
expect(di.resolve("Service")).to_equal("original")
```

</details>

#### is_locked returns true after explicit lock

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

#### is_locked returns false after unlock

1. di lock
   - Expected: di.is_locked() is true
2. di unlock
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
expect(di.is_locked()).to_equal(true)
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

### DI Error Cases: missing key fallback

#### resolve_or returns default text for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
val result = di.resolve_or("nonexistent_key", "default_val")
expect(result).to_equal("default_val")
```

</details>

#### resolve_or returns default integer for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
val result = di.resolve_or("missing_int", 42)
expect(result).to_equal(42)
```

</details>

#### has returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
expect(di.has_binding("definitely_not_there")).to_equal(false)
```

</details>

#### resolve_or returns bound value when key exists

1. di bind instance
   - Expected: result equals `found_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("existing", "found_value")
val result = di.resolve_or("existing", "should_not_be_used")
expect(result).to_equal("found_value")
```

</details>

#### has returns true after bind_instance

1. di bind instance
   - Expected: di.has_binding("present") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("present", "value")
expect(di.has_binding("present")).to_equal(true)
```

</details>

### DI Error Cases: edge cases

#### empty string key can be stored and retrieved

1. di bind instance
   - Expected: di.resolve("") equals `empty_key_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("", "empty_key_val")
expect(di.resolve("")).to_equal("empty_key_val")
```

</details>

#### overwriting key keeps the latest value

1. di bind instance
2. di bind instance
   - Expected: di.resolve("key") equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("key", "first")
di.bind_instance("key", "second")
expect(di.resolve("key")).to_equal("second")
```

</details>

#### multiple distinct keys are independent

1. di bind instance
2. di bind instance
   - Expected: di.resolve("a") equals `val_a`
   - Expected: di.resolve("b") equals `val_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("a", "val_a")
di.bind_instance("b", "val_b")
expect(di.resolve("a")).to_equal("val_a")
expect(di.resolve("b")).to_equal("val_b")
```

</details>

#### singleton is resolved from singletons not bindings

1. di bind instance
   - Expected: di.has_binding("svc") is true
   - Expected: di.resolve("svc") equals `singleton_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("svc", "singleton_val")
expect(di.has_binding("svc")).to_equal(true)
expect(di.resolve("svc")).to_equal("singleton_val")
```

</details>

#### factory binding is callable after bind

1. di bind
   - Expected: di.has_binding("computed") is true
   - Expected: result equals `computed_result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind("computed", fn(): "computed_result")
expect(di.has_binding("computed")).to_equal(true)
val result = di.resolve("computed")
expect(result).to_equal("computed_result")
```

</details>

### DI Error Cases: resolve works through lock

#### resolve_or for existing key works when locked

1. di bind instance
2. di lock
   - Expected: result equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Config", "prod-config")
di.lock()
val result = di.resolve_or("Config", "default")
expect(result).to_equal("prod-config")
```

</details>

#### resolve_or for missing key returns default when locked

1. di lock
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
val result = di.resolve_or("NotPresent", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### resolve for pre-lock binding works after lock

1. di bind instance
2. di lock
   - Expected: di.resolve("Backend") equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Backend", "production-backend")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
```

</details>

### DI Error Cases: env-var lock rejects bindings

#### bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set

1. rt env set
2. rt env set
3. di bind instance
   - Expected: env_locked is true
4. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("MockSvc", "mock")
# Note: env-var lock not enforced in stub - checking di_is_system_test_locked instead
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### bind allowed when SIMPLE_DI_TEST=1 bypasses env lock

1. rt env set
2. rt env set
3. di bind instance
   - Expected: di.has_binding("TestMock") is true
4. rt env set
5. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("TestMock", "allowed")
expect(di.has_binding("TestMock")).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

#### di_is_system_test_locked returns false when env not set

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
