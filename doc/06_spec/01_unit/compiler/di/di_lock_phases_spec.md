# Di Lock Phases Specification

> Tests covering DiLock: Phase 1 - Basic API, DiLock: Phase 2 - Integration, DiLock: Phase 3 - System behavior.

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

- container is unlocked by default
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("container is unlocked by default")
val di = make_di()
expect(di.is_locked()).to_equal(false)
```

</details>

#### locked field is false initially

- locked field is false initially
   - Expected: di.locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locked field is false initially")
val di = make_di()
expect(di.locked).to_equal(false)
```

</details>

#### bind_instance works when unlocked

- bind_instance works when unlocked
   - Expected: di.has_binding("Service") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind_instance works when unlocked")
val di = make_di()
di.bind_instance("Service", "value")
expect(di.has_binding("Service")).to_equal(true)
```

</details>

#### lock operations

#### lock sets is_locked to true

- lock sets is_locked to true
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock sets is_locked to true")
val di = make_di()
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### lock prevents bind_instance

- lock prevents bind_instance
   - Expected: di.has_binding("Blocked") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock prevents bind_instance")
val di = make_di()
di.lock()
di.bind_instance("Blocked", "value")
expect(di.has_binding("Blocked")).to_equal(false)
```

</details>

#### lock prevents bind factory

- lock prevents bind factory
   - Expected: di.has_binding("BlockedFn") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock prevents bind factory")
val di = make_di()
di.lock()
di.bind("BlockedFn", fn(): "value")
expect(di.has_binding("BlockedFn")).to_equal(false)
```

</details>

#### lock does not clear existing bindings

- lock does not clear existing bindings
   - Expected: di.has_binding("PreLock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock does not clear existing bindings")
val di = make_di()
di.bind_instance("PreLock", "early")
di.lock()
expect(di.has_binding("PreLock")).to_equal(true)
```

</details>

#### unlock operations

#### unlock sets is_locked to false

- unlock sets is_locked to false
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unlock sets is_locked to false")
val di = make_di()
di.lock()
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### unlock allows bind_instance again

- unlock allows bind_instance again
   - Expected: di.has_binding("AfterUnlock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unlock allows bind_instance again")
val di = make_di()
di.lock()
di.unlock()
di.bind_instance("AfterUnlock", "allowed")
expect(di.has_binding("AfterUnlock")).to_equal(true)
```

</details>

#### unlock allows bind factory again

- unlock allows bind factory again
   - Expected: di.has_binding("FactoryAfter") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unlock allows bind factory again")
val di = make_di()
di.lock()
di.unlock()
di.bind("FactoryAfter", fn(): "factory-value")
expect(di.has_binding("FactoryAfter")).to_equal(true)
```

</details>

#### resolve while locked

#### resolve works on pre-lock bindings

- resolve works on pre-lock bindings
   - Expected: di.resolve("Config") equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve works on pre-lock bindings")
val di = make_di()
di.bind_instance("Config", "prod-config")
di.lock()
expect(di.resolve("Config")).to_equal("prod-config")
```

</details>

#### resolve_or works while locked

- resolve_or works while locked
   - Expected: di.resolve_or("Setting", "off") equals `on`
   - Expected: di.resolve_or("Missing", "default") equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_or works while locked")
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

- pre-lock backend binding is protected
   - Expected: di.resolve("Backend") equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pre-lock backend binding is protected")
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.lock()
di.bind_instance("Backend", "mock-backend")
expect(di.resolve("Backend")).to_equal("production-backend")
```

</details>

#### two pre-lock bindings both resolvable after lock

- two pre-lock bindings both resolvable after lock
   - Expected: di.resolve("Backend") equals `production-backend`
   - Expected: di.resolve("Logger") equals `file-logger`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two pre-lock bindings both resolvable after lock")
val di = make_di()
di.bind_instance("Backend", "production-backend")
di.bind_instance("Logger", "file-logger")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
expect(di.resolve("Logger")).to_equal("file-logger")
```

</details>

#### lock-unlock-relock cycle works

- lock-unlock-relock cycle works
   - Expected: di.has_binding("A") is true
   - Expected: di.has_binding("A") is true
   - Expected: di.has_binding("B") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock-unlock-relock cycle works")
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

- returns false when SIMPLE_SYSTEM_TEST is not 1
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when SIMPLE_SYSTEM_TEST is not 1")
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(false)
rt_env_set("SIMPLE_SYSTEM_TEST", "")
```

</details>

#### returns true when SIMPLE_SYSTEM_TEST=1 and no di_test

- returns true when SIMPLE_SYSTEM_TEST=1 and no di_test
   - Expected: di_is_system_test_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when SIMPLE_SYSTEM_TEST=1 and no di_test")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### returns false when SIMPLE_DI_TEST=1 bypasses lock

- returns false when SIMPLE_DI_TEST=1 bypasses lock
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when SIMPLE_DI_TEST=1 bypasses lock")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")
expect(di_is_system_test_locked()).to_equal(false)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

#### env-var based locking

#### env lock active when SIMPLE_SYSTEM_TEST=1

- env lock active when SIMPLE_SYSTEM_TEST=1
   - Expected: env_locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock active when SIMPLE_SYSTEM_TEST=1")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### env lock not active when SIMPLE_DI_TEST=1

- env lock not active when SIMPLE_DI_TEST=1
   - Expected: env_locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock not active when SIMPLE_DI_TEST=1")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "1")
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(false)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")
```

</details>

#### no env lock when SIMPLE_SYSTEM_TEST=0

- no env lock when SIMPLE_SYSTEM_TEST=0
   - Expected: env_locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no env lock when SIMPLE_SYSTEM_TEST=0")
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(false)
```

</details>

### DiLock: Phase 3 - System behavior

#### lock as system test guard

#### locked container is_locked reflects explicit lock

- locked container is_locked reflects explicit lock
   - Expected: di.is_locked() is false
   - Expected: di.is_locked() is true
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locked container is_locked reflects explicit lock")
val di = make_di()
expect(di.is_locked()).to_equal(false)
di.lock()
expect(di.is_locked()).to_equal(true)
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

#### locked container blocks bind_tagged

- locked container blocks bind_tagged
   - Expected: di.has_binding("TaggedSvc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locked container blocks bind_tagged")
val di = make_di()
di.lock()
di.bind_tagged("TaggedSvc", ["system"], fn(): "tagged-val")
expect(di.has_binding("TaggedSvc")).to_equal(false)
```

</details>

#### has returns false for bindings rejected by lock

- has returns false for bindings rejected by lock
   - Expected: di.has_binding("NotRegistered") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has returns false for bindings rejected by lock")
val di = make_di()
di.lock()
di.bind_instance("NotRegistered", "value")
expect(di.has_binding("NotRegistered")).to_equal(false)
```

</details>

#### lock preserves resolve_or semantics

#### resolve_or returns pre-lock value when locked

- resolve_or returns pre-lock value when locked
   - Expected: result equals `registered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_or returns pre-lock value when locked")
val di = make_di()
di.bind_instance("Svc", "registered")
di.lock()
val result = di.resolve_or("Svc", "default")
expect(result).to_equal("registered")
```

</details>

#### resolve_or returns default for missing when locked

- resolve_or returns default for missing when locked
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_or returns default for missing when locked")
val di = make_di()
di.lock()
val result = di.resolve_or("Absent", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### env-var cleanup

#### env lock only active when SIMPLE_SYSTEM_TEST=1

- env lock only active when SIMPLE_SYSTEM_TEST=1
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock only active when SIMPLE_SYSTEM_TEST=1")
rt_env_set("SIMPLE_SYSTEM_TEST", "")
rt_env_set("SIMPLE_DI_TEST", "")
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### env lock active then cleared works

- env lock active then cleared works
   - Expected: di_is_system_test_locked() is true
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock active then cleared works")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### di_test bypass only works when system_test is also 1

- di_test bypass only works when system_test is also 1
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("di_test bypass only works when system_test is also 1")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DiLock: Phase 1 - Basic API, DiLock: Phase 2 - Integration, DiLock: Phase 3 - System behavior.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e9ddedad9c9f9de9689d2ba8d8420946d820ccddd47ee0a39c72bc830955e610`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9ddedad9c9f9de9689d2ba8d8420946d820ccddd47ee0a39c72bc830955e610`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9ddedad9c9f9de9689d2ba8d8420946d820ccddd47ee0a39c72bc830955e610`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/di/di_lock_phases_spec.spl
mirror: doc/06_spec/01_unit/compiler/di/di_lock_phases_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/di/di_lock_phases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/di/di_lock_phases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/di/di_lock_phases_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'container is unlocked by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/di/di_lock_phases_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'locked field is false initially' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/di/di_lock_phases_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bind_instance works when unlocked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
