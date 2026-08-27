# DI System Test Lock - All Phases

> Comprehensive phase tests for the DI system test lock feature covering all five phases: lock state transitions (lock/unlock/cycle), binding rejection when locked (bind_instance, bind, bind_tagged), resolution behavior while locked (resolve, resolve_or, has), lock integration with registration protection, and full DI lifecycle including environment variable lock with SIMPLE_DI_TEST bypass.

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
| Source | `test/feature/usage/di_lock_all_phases_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive phase tests for the DI system test lock feature covering all five
phases: lock state transitions (lock/unlock/cycle), binding rejection when locked
(bind_instance, bind, bind_tagged), resolution behavior while locked (resolve,
resolve_or, has), lock integration with registration protection, and full DI
lifecycle including environment variable lock with SIMPLE_DI_TEST bypass.

## Syntax

```simple
use std.spec.step

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

- new container is unlocked
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("new container is unlocked")
val di = make_di()
expect(di.is_locked()).to_equal(false)
```

</details>

#### locked field is false on construction

- locked field is false on construction
   - Expected: di.locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("locked field is false on construction")
val di = make_di()
expect(di.locked).to_equal(false)
```

</details>

#### binding works before any lock

- binding works before any lock
   - Expected: di.has_binding("Svc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binding works before any lock")
val di = make_di()
di.bind_instance("Svc", "value")
expect(di.has_binding("Svc")).to_equal(true)
```

</details>

#### lock transitions

#### lock sets is_locked to true

- lock sets is_locked to true
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lock sets is_locked to true")
val di = make_di()
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### unlock after lock sets is_locked to false

- unlock after lock sets is_locked to false
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unlock after lock sets is_locked to false")
val di = make_di()
di.lock()
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### multiple lock calls remain locked

- multiple lock calls remain locked
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple lock calls remain locked")
val di = make_di()
di.lock()
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### unlock without prior lock stays unlocked

- unlock without prior lock stays unlocked
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unlock without prior lock stays unlocked")
val di = make_di()
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### lock-unlock-lock cycle ends locked

- lock-unlock-lock cycle ends locked
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lock-unlock-lock cycle ends locked")
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

- bind_instance rejected when locked
   - Expected: di.has_binding("Blocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bind_instance rejected when locked")
val di = make_di()
di.lock()
di.bind_instance("Blocked", "value")
expect(di.has_binding("Blocked")).to_equal(false)
```

</details>

#### bind_instance succeeds before lock

- bind_instance succeeds before lock
   - Expected: di.has_binding("PreLock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bind_instance succeeds before lock")
val di = make_di()
di.bind_instance("PreLock", "early")
di.lock()
expect(di.has_binding("PreLock")).to_equal(true)
```

</details>

#### bind factory is blocked

#### bind factory rejected when locked

- bind factory rejected when locked
   - Expected: di.has_binding("FactoryBlocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bind factory rejected when locked")
val di = make_di()
di.lock()
di.bind("FactoryBlocked", fn(): "factory-val")
expect(di.has_binding("FactoryBlocked")).to_equal(false)
```

</details>

#### bind_tagged rejected when locked

- bind_tagged rejected when locked
   - Expected: di.has_binding("TaggedBlocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bind_tagged rejected when locked")
val di = make_di()
di.lock()
di.bind_tagged("TaggedBlocked", ["system"], fn(): "tagged-val")
expect(di.has_binding("TaggedBlocked")).to_equal(false)
```

</details>

#### bind allowed after unlock

#### bind_instance works after unlock

- bind_instance works after unlock
   - Expected: di.has_binding("Blocked") is false
   - Expected: di.has_binding("Allowed") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bind_instance works after unlock")
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

- bind factory works after unlock
   - Expected: di.has_binding("FactoryAfterUnlock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("bind factory works after unlock")
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

- resolve pre-lock singleton works
   - Expected: di.resolve("Config") equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolve pre-lock singleton works")
val di = make_di()
di.bind_instance("Config", "prod-config")
di.lock()
expect(di.resolve("Config")).to_equal("prod-config")
```

</details>

#### resolve pre-lock factory works

- resolve pre-lock factory works
   - Expected: di.resolve("Builder") equals `built-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolve pre-lock factory works")
val di = make_di()
di.bind("Builder", fn(): "built-value")
di.lock()
expect(di.resolve("Builder")).to_equal("built-value")
```

</details>

#### resolve_or works while locked

#### resolve_or returns registered value when locked

- resolve_or returns registered value when locked
   - Expected: di.resolve_or("Setting", "off") equals `on`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolve_or returns registered value when locked")
val di = make_di()
di.bind_instance("Setting", "on")
di.lock()
expect(di.resolve_or("Setting", "off")).to_equal("on")
```

</details>

#### resolve_or returns default for missing when locked

- resolve_or returns default for missing when locked
   - Expected: di.resolve_or("Missing", "fallback") equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolve_or returns default for missing when locked")
val di = make_di()
di.lock()
expect(di.resolve_or("Missing", "fallback")).to_equal("fallback")
```

</details>

#### has works correctly

#### has returns true for pre-lock binding

- has returns true for pre-lock binding
   - Expected: di.has_binding("Present") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has returns true for pre-lock binding")
val di = make_di()
di.bind_instance("Present", "here")
di.lock()
expect(di.has_binding("Present")).to_equal(true)
```

</details>

#### has returns false for post-lock rejected binding

- has returns false for post-lock rejected binding
   - Expected: di.has_binding("Rejected") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has returns false for post-lock rejected binding")
val di = make_di()
di.lock()
di.bind_instance("Rejected", "nope")
expect(di.has_binding("Rejected")).to_equal(false)
```

</details>

### DI Lock: Phase 4 - Lock integration with registration

#### protects production bindings

#### pre-lock binding cannot be overwritten while locked

- pre-lock binding cannot be overwritten while locked
   - Expected: di.resolve("Backend") equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pre-lock binding cannot be overwritten while locked")
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.lock()
di.bind_instance("Backend", "mock-backend")
expect(di.resolve("Backend")).to_equal("production-backend")
```

</details>

#### multiple pre-lock bindings all resolvable after lock

- multiple pre-lock bindings all resolvable after lock
   - Expected: di.resolve("Backend") equals `production-backend`
   - Expected: di.resolve("Logger") equals `file-logger`
   - Expected: di.resolve("Config") equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple pre-lock bindings all resolvable after lock")
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

- new bindings added after unlock are accessible
   - Expected: di.has_binding("First") is true
   - Expected: di.has_binding("Second") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("new bindings added after unlock are accessible")
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

- lock-unlock-relock preserves all accumulated bindings
   - Expected: di.resolve("A") equals `first`
   - Expected: di.resolve("B") equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lock-unlock-relock preserves all accumulated bindings")
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

- di_is_system_test_locked returns false normally
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("di_is_system_test_locked returns false normally")
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(false)
rt_env_set("SIMPLE_SYSTEM_TEST", "")
```

</details>

#### env lock is active when system test active

- env lock is active when system test active
   - Expected: env_locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env lock is active when system test active")
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

- full DI lifecycle: register, lock, resolve, unlock, extend
   - Expected: di.is_locked() is true
   - Expected: di.resolve("logger") equals `console_logger`
   - Expected: di.resolve("config") equals `prod_config`
   - Expected: di.resolve("parser") equals `default_parser`
   - Expected: di.has_binding("extra") is false
   - Expected: di.is_locked() is false
   - Expected: di.resolve("extra") equals `new_service`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("full DI lifecycle: register, lock, resolve, unlock, extend")
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

- resolve_or covers missing services during operation
   - Expected: logger equals `syslog`
   - Expected: tracer equals `noop_tracer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolve_or covers missing services during operation")
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

- has correctly reflects what is and is not registered
   - Expected: di.has_binding("ServiceA") is true
   - Expected: di.has_binding("ServiceB") is true
   - Expected: di.has_binding("ServiceC") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has correctly reflects what is and is not registered")
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

- env lock reflects env state then resets
   - Expected: di_is_system_test_locked() is true
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env lock reflects env state then resets")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
# After clearing env, env lock is off
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### SIMPLE_DI_TEST=1 bypass disables env lock

- SIMPLE_DI_TEST=1 bypass disables env lock
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("SIMPLE_DI_TEST=1 bypass disables env lock")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a856a604ef4f0d51152983dd0ea0e9bfb3c51aa770b7d050bfc1381bcd18384d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a856a604ef4f0d51152983dd0ea0e9bfb3c51aa770b7d050bfc1381bcd18384d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a856a604ef4f0d51152983dd0ea0e9bfb3c51aa770b7d050bfc1381bcd18384d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/di_lock_all_phases_spec.spl
mirror: doc/06_spec/feature/usage/di_lock_all_phases_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/di_lock_all_phases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/di_lock_all_phases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/di_lock_all_phases_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new container is unlocked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/di_lock_all_phases_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locked field is false on construction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/di_lock_all_phases_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binding works before any lock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
