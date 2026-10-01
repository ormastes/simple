# Di Runtime Specification

> Tests covering DI Runtime, registration and resolution, singleton caching, cascade forcing, cycle detection, reset, stats, service_names, missing service.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Runtime Specification

## Scenarios

### DI Runtime

### registration and resolution

#### registers and resolves an eager service

- registers and resolves an eager service
   - Expected: result equals `hello_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers and resolves an eager service")
di_reset()
di_register("svc_a", fn(): "hello_a", false)
val result = di_resolve("svc_a")
expect(result).to_equal("hello_a")
```

</details>

#### registers and resolves a lazy service

- registers and resolves a lazy service
   - Expected: result equals `hello_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers and resolves a lazy service")
di_reset()
di_register("svc_b", fn(): "hello_b", true)
val result = di_resolve("svc_b")
expect(result).to_equal("hello_b")
```

</details>

#### reports registered services

- reports registered services
   - Expected: di_is_registered("svc_c") is true
   - Expected: di_is_registered("nonexistent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports registered services")
di_reset()
di_register("svc_c", fn(): 42, false)
expect(di_is_registered("svc_c")).to_equal(true)
expect(di_is_registered("nonexistent")).to_equal(false)
```

</details>

### singleton caching

#### returns the same instance on repeated resolve

- returns the same instance on repeated resolve
   - Expected: first equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the same instance on repeated resolve")
di_reset()
var call_count = 0
di_register("cached", fn():
    call_count = call_count + 1
    "instance_{call_count}"
, true)
val first = di_resolve("cached")
val second = di_resolve("cached")
expect(first).to_equal(second)
```

</details>

#### eager services are instantiated at registration

- eager services are instantiated at registration
   - Expected: result equals `eager_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eager services are instantiated at registration")
di_reset()
di_register("eager_svc", fn(): "eager_val", false)
# Should be cached already - no force needed
val result = di_resolve("eager_svc")
expect(result).to_equal("eager_val")
```

</details>

### cascade forcing

#### forces transitive dependencies

- forces transitive dependencies
   - Expected: result equals `a_uses_b_uses_leaf_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forces transitive dependencies")
di_reset()
di_register("dep_c", fn(): "leaf_value", true)
di_register("dep_b", fn():
    val c = di_resolve("dep_c")
    "b_uses_{c}"
, true)
di_register("dep_a", fn():
    val b = di_resolve("dep_b")
    "a_uses_{b}"
, true)
val result = di_resolve("dep_a")
expect(result).to_equal("a_uses_b_uses_leaf_value")
```

</details>

### cycle detection

#### detects circular dependencies

- detects circular dependencies
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects circular dependencies")
di_reset()
di_register("cycle_a", fn():
    di_resolve("cycle_b")
, true)
di_register("cycle_b", fn():
    di_resolve("cycle_a")
, true)
# This should print an error and return nil instead of infinite loop
val result = di_resolve("cycle_a")
expect(result).to_equal(nil)
```

</details>

### reset

#### clears all registered services

- clears all registered services
   - Expected: di_is_registered("temp") is true
   - Expected: di_is_registered("temp") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all registered services")
di_reset()
di_register("temp", fn(): "temp_val", false)
expect(di_is_registered("temp")).to_equal(true)
di_reset()
expect(di_is_registered("temp")).to_equal(false)
```

</details>

#### resets force count

- resets force count
   - Expected: di_force_count() > 0 is true
   - Expected: di_force_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets force count")
di_reset()
di_register("lazy_svc", fn(): "val", true)
di_resolve("lazy_svc")
expect(di_force_count() > 0).to_equal(true)
di_reset()
expect(di_force_count()).to_equal(0)
```

</details>

### stats

#### returns diagnostic info

- returns diagnostic info
   - Expected: info contains `2 registered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns diagnostic info")
di_reset()
di_register("s1", fn(): "v1", true)
di_register("s2", fn(): "v2", false)
val info = di_stats()
expect(info.contains("2 registered")).to_equal(true)
```

</details>

### service_names

#### lists registered service names

- lists registered service names
   - Expected: names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists registered service names")
di_reset()
di_register("alpha", fn(): 1, true)
di_register("beta", fn(): 2, false)
val names = di_service_names()
expect(names.len()).to_equal(2)
```

</details>

### missing service

#### returns nil for unregistered service

- returns nil for unregistered service
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unregistered service")
di_reset()
val result = di_resolve("nonexistent")
expect(result).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/di/di_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DI Runtime, registration and resolution, singleton caching, cascade forcing, cycle detection, reset, stats, service_names, missing service.
- DI Runtime
- registration and resolution
- singleton caching
- cascade forcing
- cycle detection
- reset
- stats
- service_names
- missing service

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `942c79a3d249ba70fa2dd5fdc651d678c3612949483115f370279d7ab075fff4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `942c79a3d249ba70fa2dd5fdc651d678c3612949483115f370279d7ab075fff4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `942c79a3d249ba70fa2dd5fdc651d678c3612949483115f370279d7ab075fff4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/di/di_runtime_spec.spl
mirror: doc/06_spec/unit/compiler/di/di_runtime_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/di/di_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/di/di_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/di/di_runtime_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/di/di_runtime_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers and resolves an eager service' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/di/di_runtime_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers and resolves a lazy service' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/di/di_runtime_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports registered services' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
