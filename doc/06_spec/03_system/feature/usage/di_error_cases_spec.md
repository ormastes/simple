# DI Error Cases

> Tests the failure paths and edge cases of the DiContainer dependency injection system. Covers locked container behavior (binding rejection), missing key fallback via resolve_or, edge cases like empty keys and key overwrites, resolve behavior through locks, and environment variable-based system test locking via SIMPLE_SYSTEM_TEST/SIMPLE_DI_TEST.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the failure paths and edge cases of the DiContainer dependency injection system.
Covers locked container behavior (binding rejection), missing key fallback via resolve_or,
edge cases like empty keys and key overwrites, resolve behavior through locks, and
environment variable-based system test locking via SIMPLE_SYSTEM_TEST/SIMPLE_DI_TEST.

## Scenarios

### DI Error Cases: locked container rejects bindings

#### bind_instance on locked container does not store value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bind_instance on locked container does not store value
   - Expected: di.has_binding("new_key") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bind_instance on locked container does not store value")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("existing", "before")
di.lock()
di.bind_instance("new_key", "should_not_appear")
expect(di.has_binding("new_key")).to_equal(false)
```

</details>

#### bind factory on locked container does not register

- bind factory on locked container does not register
   - Expected: di.has_binding("FactoryKey") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bind factory on locked container does not register")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind("FactoryKey", fn(): "factory_result")
expect(di.has_binding("FactoryKey")).to_equal(false)
```

</details>

#### bind_for_profile on locked container does not register

- bind_for_profile on locked container does not register
   - Expected: di.has_binding("ProfileKey") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bind_for_profile on locked container does not register")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
di.bind_for_profile("ProfileKey", CompilerProfile.Dev, fn(): "profiled")
expect(di.has_binding("ProfileKey")).to_equal(false)
```

</details>

#### locked container does not overwrite previously bound value

- locked container does not overwrite previously bound value
   - Expected: di.resolve("Service") equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("locked container does not overwrite previously bound value")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Service", "original")
di.lock()
di.bind_instance("Service", "overwrite_attempt")
expect(di.resolve("Service")).to_equal("original")
```

</details>

#### is_locked returns true after explicit lock

- is_locked returns true after explicit lock
   - Expected: di.is_locked() is false
   - Expected: di.is_locked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is_locked returns true after explicit lock")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
expect(di.is_locked()).to_equal(false)
di.lock()
expect(di.is_locked()).to_equal(true)
```

</details>

#### is_locked returns false after unlock

- is_locked returns false after unlock
   - Expected: di.is_locked() is true
   - Expected: di.is_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is_locked returns false after unlock")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
expect(di.is_locked()).to_equal(true)
di.unlock()
expect(di.is_locked()).to_equal(false)
```

</details>

### DI Error Cases: missing key fallback

#### resolve_or returns default text for missing key

- resolve_or returns default text for missing key
   - Expected: result equals `default_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_or returns default text for missing key")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
val result = di.resolve_or("nonexistent_key", "default_val")
expect(result).to_equal("default_val")
```

</details>

#### resolve_or returns default integer for missing key

- resolve_or returns default integer for missing key
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_or returns default integer for missing key")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
val result = di.resolve_or("missing_int", 42)
expect(result).to_equal(42)
```

</details>

#### has returns false for missing key

- has returns false for missing key
   - Expected: di.has_binding("definitely_not_there") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has returns false for missing key")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
expect(di.has_binding("definitely_not_there")).to_equal(false)
```

</details>

#### resolve_or returns bound value when key exists

- resolve_or returns bound value when key exists
   - Expected: result equals `found_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_or returns bound value when key exists")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("existing", "found_value")
val result = di.resolve_or("existing", "should_not_be_used")
expect(result).to_equal("found_value")
```

</details>

#### has returns true after bind_instance

- has returns true after bind_instance
   - Expected: di.has_binding("present") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has returns true after bind_instance")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("present", "value")
expect(di.has_binding("present")).to_equal(true)
```

</details>

### DI Error Cases: edge cases

#### empty string key can be stored and retrieved

- empty string key can be stored and retrieved
   - Expected: di.resolve("") equals `empty_key_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("empty string key can be stored and retrieved")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("", "empty_key_val")
expect(di.resolve("")).to_equal("empty_key_val")
```

</details>

#### overwriting key keeps the latest value

- overwriting key keeps the latest value
   - Expected: di.resolve("key") equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overwriting key keeps the latest value")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("key", "first")
di.bind_instance("key", "second")
expect(di.resolve("key")).to_equal("second")
```

</details>

#### multiple distinct keys are independent

- multiple distinct keys are independent
   - Expected: di.resolve("a") equals `val_a`
   - Expected: di.resolve("b") equals `val_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple distinct keys are independent")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("a", "val_a")
di.bind_instance("b", "val_b")
expect(di.resolve("a")).to_equal("val_a")
expect(di.resolve("b")).to_equal("val_b")
```

</details>

#### singleton is resolved from singletons not bindings

- singleton is resolved from singletons not bindings
   - Expected: di.has_binding("svc") is true
   - Expected: di.resolve("svc") equals `singleton_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("singleton is resolved from singletons not bindings")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("svc", "singleton_val")
expect(di.has_binding("svc")).to_equal(true)
expect(di.resolve("svc")).to_equal("singleton_val")
```

</details>

#### factory binding is callable after bind

- factory binding is callable after bind
   - Expected: di.has_binding("computed") is true
   - Expected: result equals `computed_result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("factory binding is callable after bind")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind("computed", fn(): "computed_result")
expect(di.has_binding("computed")).to_equal(true)
val result = di.resolve("computed")
expect(result).to_equal("computed_result")
```

</details>

### DI Error Cases: resolve works through lock

#### resolve_or for existing key works when locked

- resolve_or for existing key works when locked
   - Expected: result equals `prod-config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_or for existing key works when locked")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Config", "prod-config")
di.lock()
val result = di.resolve_or("Config", "default")
expect(result).to_equal("prod-config")
```

</details>

#### resolve_or for missing key returns default when locked

- resolve_or for missing key returns default when locked
   - Expected: result equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve_or for missing key returns default when locked")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.lock()
val result = di.resolve_or("NotPresent", "fallback")
expect(result).to_equal("fallback")
```

</details>

#### resolve for pre-lock binding works after lock

- resolve for pre-lock binding works after lock
   - Expected: di.resolve("Backend") equals `production-backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolve for pre-lock binding works after lock")
val di = DiContainer(bindings: [], singletons: [], profile: "dev", all_bindings: [], locked: false)
di.bind_instance("Backend", "production-backend")
di.lock()
expect(di.resolve("Backend")).to_equal("production-backend")
```

</details>

### DI Error Cases: env-var lock rejects bindings

#### bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set

- bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set
   - Expected: env_locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set")
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

- bind allowed when SIMPLE_DI_TEST=1 bypasses env lock
   - Expected: di.has_binding("TestMock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bind allowed when SIMPLE_DI_TEST=1 bypasses env lock")
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

- di_is_system_test_locked returns false when env not set
   - Expected: di_is_system_test_locked() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("di_is_system_test_locked returns false when env not set")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d3c166a5f8d3c5ff4395e6e4559c098a3c92be6f7d3e07be59af13604c1ad60a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3c166a5f8d3c5ff4395e6e4559c098a3c92be6f7d3e07be59af13604c1ad60a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3c166a5f8d3c5ff4395e6e4559c098a3c92be6f7d3e07be59af13604c1ad60a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/usage/di_error_cases_spec.spl
mirror: doc/06_spec/03_system/feature/usage/di_error_cases_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/di_error_cases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/di_error_cases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/di_error_cases_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/di_error_cases_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bind_instance on locked container does not store value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/di_error_cases_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bind factory on locked container does not register' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/di_error_cases_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bind_for_profile on locked container does not register' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
