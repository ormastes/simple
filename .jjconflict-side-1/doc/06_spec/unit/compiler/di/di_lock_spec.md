# Di Lock Specification

> Tests covering DI Container Lock, explicit lock, env-var based lock, di_is_system_test_locked, locked preserves existing bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Lock Specification

## Scenarios

### DI Container Lock

### explicit lock

#### blocks bind when locked

- blocks bind when locked
   - Expected: di.has_binding("Foo") is true
   - Expected: di.has_binding("Bar") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks bind when locked")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Foo", 42)
expect(di.has_binding("Foo")).to_equal(true)

di.lock()
di.bind_instance("Bar", 99)
expect(di.has_binding("Bar")).to_equal(false)
```

</details>

#### blocks bind factory when locked

- blocks bind factory when locked
   - Expected: di.has_binding("Baz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks bind factory when locked")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind("Baz", fn(): 123)
expect(di.has_binding("Baz")).to_equal(false)
```

</details>

#### allows bind after unlock

- allows bind after unlock
   - Expected: di.has_binding("Foo") is false
   - Expected: di.has_binding("Foo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows bind after unlock")
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

- is_locked returns true when locked
   - Expected: di.is_locked() is false
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_locked returns true when locked")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
expect(di.is_locked()).to_equal(false)
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### resolve still works when locked

- resolve still works when locked
   - Expected: di.resolve("Svc") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve still works when locked")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Svc", "hello")
di.lock()
expect(di.resolve("Svc")).to_equal("hello")
```

</details>

#### well-behaved caller never reaches the guarded bind path while locked

- well-behaved caller never reaches the guarded bind path while locked
   - Expected: di.has_binding("Bar") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("well-behaved caller never reaches the guarded bind path while locked")
# A caller that respects the lock (checks is_locked() first) must
# never invoke bind_instance_guarded while locked — the prevention
# mock stays green, proving no code path silently records a
# locked-mutation attempt. See the sabotage recipe (deleted after
# use) for proof this guard actually fires when that invariant is
# violated: bind_instance_guarded called unconditionally while
# locked reports `forbidden call: di_bind_while_locked called 1x
# (allowed 0) — DI mutation while locked must be rejected, not
# recorded` and fails the example.
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
val guard_mock = MockFunction.new("di_bind_while_locked")
di.lock()
if not di.is_locked():
    di.bind_instance_guarded("Bar", 99, guard_mock)
expect(di.has_binding("Bar")).to_equal(false)
prevent(guard_mock, "DI mutation while locked must be rejected, not recorded")
```

</details>

### env-var based lock

#### env lock active when SIMPLE_SYSTEM_TEST=1

- env lock active when SIMPLE_SYSTEM_TEST=1
   - Expected: env_locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock active when SIMPLE_SYSTEM_TEST=1")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")

val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(true)

# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### env lock not active when SIMPLE_SYSTEM_TEST=0

- env lock not active when SIMPLE_SYSTEM_TEST=0
   - Expected: env_locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock not active when SIMPLE_SYSTEM_TEST=0")
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
rt_env_set("SIMPLE_DI_TEST", "0")

val env_locked = di_is_system_test_locked()
expect(env_locked).to_equal(false)
```

</details>

#### env lock bypassed when SIMPLE_DI_TEST=1

- env lock bypassed when SIMPLE_DI_TEST=1
   - Expected: env_locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock bypassed when SIMPLE_DI_TEST=1")
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

- env lock state changes with env vars
   - Expected: di_is_system_test_locked() is true
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env lock state changes with env vars")
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

- returns false when no env var set
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when no env var set")
rt_env_set("SIMPLE_SYSTEM_TEST", "")
rt_env_set("SIMPLE_DI_TEST", "")
expect(di_is_system_test_locked()).to_equal(false)
```

</details>

#### returns true when system test without di_test

- returns true when system test without di_test
   - Expected: di_is_system_test_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when system test without di_test")
rt_env_set("SIMPLE_SYSTEM_TEST", "1")
rt_env_set("SIMPLE_DI_TEST", "0")
expect(di_is_system_test_locked()).to_equal(true)

# Cleanup
rt_env_set("SIMPLE_SYSTEM_TEST", "0")
```

</details>

#### returns false when di_test allows

- returns false when di_test allows
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when di_test allows")
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

- pre-lock bindings remain resolvable
   - Expected: di.resolve("Backend") equals `production-backend`
   - Expected: di.resolve("Logger") equals `file-logger`
   - Expected: di.resolve("Backend") equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pre-lock bindings remain resolvable")
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

- resolve_or works when locked
   - Expected: di.resolve_or("Config", "default") equals `prod-config`
   - Expected: di.resolve_or("Missing", "fallback") equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_or works when locked")
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
| Source | `test/unit/compiler/di/di_lock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DI Container Lock, explicit lock, env-var based lock, di_is_system_test_locked, locked preserves existing bindings.
- DI Container Lock
- explicit lock
- env-var based lock
- di_is_system_test_locked
- locked preserves existing bindings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `ee080ae1855b1878db25fea3eb21663d24eacce472bfd23d638a52b98ed85e8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee080ae1855b1878db25fea3eb21663d24eacce472bfd23d638a52b98ed85e8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee080ae1855b1878db25fea3eb21663d24eacce472bfd23d638a52b98ed85e8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/di/di_lock_spec.spl
mirror: doc/06_spec/unit/compiler/di/di_lock_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/di/di_lock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/di/di_lock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/di/di_lock_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks bind when locked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/di/di_lock_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks bind factory when locked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/di/di_lock_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows bind after unlock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
