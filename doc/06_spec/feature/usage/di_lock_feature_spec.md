# DI Lock Feature

> Tests the DiContainer lock/unlock mechanism across all phases: lock state transitions, locked behavior that rejects new bindings while allowing resolution, lock semantics including pre-lock binding preservation and overwrite protection, integration with environment variable locking, and a complete system test covering the full registration-lock-resolve-unlock-extend lifecycle.

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
| Source | `test/feature/usage/di_lock_feature_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the DiContainer lock/unlock mechanism across all phases: lock state
transitions, locked behavior that rejects new bindings while allowing resolution,
lock semantics including pre-lock binding preservation and overwrite protection,
integration with environment variable locking, and a complete system test
covering the full registration-lock-resolve-unlock-extend lifecycle.

## Syntax

```simple
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts unlocked
   - Expected: di.locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("starts unlocked")
val di = make_di()
expect(di.locked).to_equal(false)
```

</details>

#### lock() transitions to locked state

- lock() transitions to locked state
   - Expected: di.locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lock() transitions to locked state")
val di = make_di()
di.lock()
expect(di.locked).to_equal(true)
```

</details>

#### is_locked() returns true after lock

- is_locked() returns true after lock
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_locked() returns true after lock")
val di = make_di()
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### unlock() transitions back to unlocked

- unlock() transitions back to unlocked
   - Expected: di.locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unlock() transitions back to unlocked")
val di = make_di()
di.lock()
di.unlock()
expect(di.locked).to_equal(false)
```

</details>

#### is_locked() returns false after unlock

- is_locked() returns false after unlock
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_locked() returns false after unlock")
val di = make_di()
di.lock()
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### is_locked() returns false on fresh container

- is_locked() returns false on fresh container
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_locked() returns false on fresh container")
val di = make_di()
expect(di.is_locked()).to_equal(false)
```

</details>

### DI Lock Feature: Phase 2 - Locked behavior

#### locked container rejects bind_instance

- locked container rejects bind_instance
   - Expected: di.has_binding("Bar") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container rejects bind_instance")
val di = make_di()
di.lock()
di.bind_instance("Bar", 99)
expect(di.has_binding("Bar")).to_equal(false)
```

</details>

#### locked container rejects bind

- locked container rejects bind
   - Expected: di.has_binding("Baz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container rejects bind")
val di = make_di()
di.lock()
di.bind("Baz", fn(): 123)
expect(di.has_binding("Baz")).to_equal(false)
```

</details>

#### locked container still allows resolve

- locked container still allows resolve
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container still allows resolve")
val di = make_di()
di.bind_instance("Svc", "hello")
di.lock()
val result = di.resolve("Svc")
expect(result).to_equal("hello")
```

</details>

#### locked container still allows resolve_or

- locked container still allows resolve_or
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container still allows resolve_or")
val di = make_di()
di.bind_instance("Svc", "hello")
di.lock()
val result = di.resolve_or("Svc", "default")
expect(result).to_equal("hello")
```

</details>

#### locked container still allows has check

- locked container still allows has check
   - Expected: di.has_binding("Svc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container still allows has check")
val di = make_di()
di.bind_instance("Svc", "hello")
di.lock()
expect(di.has_binding("Svc")).to_equal(true)
```

</details>

#### locked container resolve_or returns default for missing

- locked container resolve_or returns default for missing
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container resolve_or returns default for missing")
val di = make_di()
di.lock()
val result = di.resolve_or("Missing", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### locked container rejects bind_tagged

- locked container rejects bind_tagged
   - Expected: di.has_binding("Tagged") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container rejects bind_tagged")
val di = make_di()
di.lock()
di.bind_tagged("Tagged", ["api"], fn(): "tagged-val")
expect(di.has_binding("Tagged")).to_equal(false)
```

</details>

### DI Lock Feature: Phase 3 - Lock semantics

#### can lock and unlock multiple times

- can lock and unlock multiple times
   - Expected: di.is_locked() is true
   - Expected: di.is_locked() is false
   - Expected: di.is_locked() is true
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can lock and unlock multiple times")
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

- bindings before lock are preserved after lock
   - Expected: di.resolve("Backend") equals `production-backend`
   - Expected: di.resolve("Logger") equals `file-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bindings before lock are preserved after lock")
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.bind_instance("Logger", "file-logger")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
expect(di.resolve("Logger")).to_equal("file-logger")
```

</details>

#### unlock allows new bindings again

- unlock allows new bindings again
   - Expected: di.has_binding("Foo") is false
   - Expected: di.has_binding("Foo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unlock allows new bindings again")
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

- pre-lock binding not overwritten when locked
   - Expected: result equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pre-lock binding not overwritten when locked")
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.lock()
di.bind_instance("Backend", "mock-backend")
val result = di.resolve("Backend")
expect(result).to_equal("production-backend")
```

</details>

#### locked state does not affect resolve_or nil default

- locked state does not affect resolve_or nil default


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked state does not affect resolve_or nil default")
val di = make_di()
di.lock()
val result = di.resolve_or("NoSuch", nil)
expect(result).to_be_nil()
```

</details>

### DI Lock Feature: Phase 4 - Integration

#### container locked after setup phase

- container locked after setup phase
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("container locked after setup phase")
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

- runtime resolution works on locked container
   - Expected: result equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("runtime resolution works on locked container")
val di = make_di()
di.bind_instance("Config", "prod-config")
di.lock()
val result = di.resolve("Config")
expect(result).to_equal("prod-config")
```

</details>

#### locked container with resolve_singleton works

- locked container with resolve_singleton works
   - Expected: result equals `singleton-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked container with resolve_singleton works")
val di = make_di()
di.bind("Singleton", fn(): "singleton-value")
di.lock()
val result = di.resolve("Singleton")
expect(result).to_equal("singleton-value")
```

</details>

#### multiple services still resolvable after lock

- multiple services still resolvable after lock
   - Expected: di.resolve("A") equals `alpha`
   - Expected: di.resolve("B") equals `beta`
   - Expected: di.resolve("C") equals `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple services still resolvable after lock")
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

- env-var lock is active when system test active
   - Expected: env_locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env-var lock is active when system test active")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(true)
# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### env-var di_test bypass disables env lock

- env-var di_test bypass disables env lock
   - Expected: env_locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env-var di_test bypass disables env lock")
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

- full registration-lock-resolve cycle works
   - Expected: di.is_locked() is true
   - Expected: di.resolve("key1") equals `val1`
   - Expected: di.resolve("key2") equals `val2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("full registration-lock-resolve cycle works")
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

- complete lifecycle: register, lock, reject, unlock, register again
   - Expected: di.is_locked() is true
   - Expected: di.has_binding("Extra") is false
   - Expected: di.resolve("Core") equals `core-impl`
   - Expected: di.has_binding("Extra") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("complete lifecycle: register, lock, reject, unlock, register again")
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

- factory bindings registered before lock resolve correctly
   - Expected: result equals `created-on-demand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("factory bindings registered before lock resolve correctly")
val di = make_di()
di.bind("LazyService", fn(): "created-on-demand")
di.lock()
val result = di.resolve("LazyService")
expect(result).to_equal("created-on-demand")
```

</details>

#### di_is_system_test_locked returns false with no env vars

- di_is_system_test_locked returns false with no env vars
   - Expected: locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("di_is_system_test_locked returns false with no env vars")
rt_env_set("SIMPLE_SYSTEM_TEST", "")
rt_env_set("SIMPLE_DI_TEST", "")
val locked = di_is_system_test_locked()
expect(locked).to_equal(false)
```

</details>

#### di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1

- di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1
   - Expected: locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78ad3f7a7ce3a88fe80d37e0d5a8344446a50b571ffd22e67b5a63d1717e2118`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78ad3f7a7ce3a88fe80d37e0d5a8344446a50b571ffd22e67b5a63d1717e2118`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78ad3f7a7ce3a88fe80d37e0d5a8344446a50b571ffd22e67b5a63d1717e2118`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/feature/usage/di_lock_feature_spec.spl
mirror: doc/06_spec/feature/usage/di_lock_feature_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/di_lock_feature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/di_lock_feature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/di_lock_feature_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts unlocked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/di_lock_feature_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lock() transitions to locked state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/di_lock_feature_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_locked() returns true after lock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/di_lock_feature_spec.spl:242:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can lock and unlock multiple times' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
