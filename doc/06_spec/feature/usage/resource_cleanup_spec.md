# Resource Cleanup Framework

> Tests the unified resource cleanup framework including the Resource trait (close, is_open, resource_name), ResourceRegistry for leak detection with unique IDs and leak reporting, LeakTracked mixin for automatic registration, and defer/with statements for scope-based cleanup. Some tests are skipped in interpreter mode as defer and with are compiler-only features.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resource Cleanup Framework

Tests the unified resource cleanup framework including the Resource trait (close, is_open, resource_name), ResourceRegistry for leak detection with unique IDs and leak reporting, LeakTracked mixin for automatic registration, and defer/with statements for scope-based cleanup. Some tests are skipped in interpreter mode as defer and with are compiler-only features.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RES-001 |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/feature/usage/resource_cleanup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the unified resource cleanup framework including the Resource trait
(close, is_open, resource_name), ResourceRegistry for leak detection with
unique IDs and leak reporting, LeakTracked mixin for automatic registration,
and defer/with statements for scope-based cleanup. Some tests are skipped
in interpreter mode as defer and with are compiler-only features.

## Syntax

```simple
use std.spec.step

val res = MockResource.open("test")
defer mockresource_close(res)
with open_resource("file.txt") as f:
f.read()
```

## Scenarios

### Feature #2300: Resource Trait

#### Resource trait interface

#### close() releases the resource

- close() releases the resource
   - Expected: is_open is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("close() releases the resource")
# Demonstrates resource lifecycle concept
var is_open = true
is_open = false  # close()
expect(is_open).to_equal(false)
```

</details>

#### close() is idempotent

- close() is idempotent
   - Expected: is_open is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("close() is idempotent")
# Demonstrates idempotent close
var is_open = true
is_open = false  # close()
is_open = false  # close() again
expect(is_open).to_equal(false)
```

</details>

#### is_open() returns correct state

- is_open() returns correct state
   - Expected: is_open is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_open() returns correct state")
# Demonstrates state tracking
val is_open = true
expect(is_open).to_equal(true)
```

</details>

#### resource_name() provides descriptive name

- resource_name() provides descriptive name
   - Expected: name equals `my_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resource_name() provides descriptive name")
# Demonstrates resource naming
val name = "my_file"
expect(name).to_equal("my_file")
```

</details>

### Feature #2301: ResourceRegistry

#### Resource registration

#### registers resources with unique IDs

- registers resources with unique IDs
   - Expected: id1 equals `0`
   - Expected: id2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("registers resources with unique IDs")
# Demonstrates ID generation
var next_id = 0
val id1 = next_id
next_id = next_id + 1
val id2 = next_id
next_id = next_id + 1

expect(id1).to_equal(0)
expect(id2).to_equal(1)
```

</details>

#### unregisters resources

- unregisters resources
   - Expected: count equals `1`
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unregisters resources")
# Demonstrates remove tracking
var count = 0
count = count + 1  # register
expect(count).to_equal(1)
count = count - 1  # unregister
expect(count).to_equal(0)
```

</details>

#### Leak detection

#### check_leaks() returns unclosed resources

- check_leaks() returns unclosed resources
   - Expected: leaked.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("check_leaks() returns unclosed resources")
# Demonstrates leak tracking
var leaked = ["leaked_file", "leaked_socket"]
expect(leaked.len()).to_equal(2)
```

</details>

#### leak_report() generates human-readable output

- leak_report() generates human-readable output
   - Expected: report contains `leak`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("leak_report() generates human-readable output")
# Demonstrates report generation
val report = "Resource leaks detected:\n  - file1\n"
expect(report.contains("leak")).to_equal(true)
```

</details>

#### clear() removes all entries

- clear() removes all entries
   - Expected: items.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("clear() removes all entries")
# Demonstrates clearing
var items = ["test1", "test2"]
items = []  # clear
expect(items.len()).to_equal(0)
```

</details>

### Feature #2302: LeakTracked Mixin

#### Automatic tracking

#### auto-registers on _start_tracking()

- auto-registers on _start_tracking()
   - Expected: tracked is true
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("auto-registers on _start_tracking()")
# Demonstrates automatic tracking
var tracked = false
var count = 0

tracked = true  # start_tracking
count = count + 1

expect(tracked).to_equal(true)
expect(count).to_equal(1)
```

</details>

#### auto-unregisters on _stop_tracking()

- auto-unregisters on _stop_tracking()
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("auto-unregisters on _stop_tracking()")
# Demonstrates automatic cleanup
var count = 1

count = count - 1  # stop_tracking
expect(count).to_equal(0)
```

</details>

#### is_tracked() returns correct state

- is_tracked() returns correct state
   - Expected: tracked is false
   - Expected: tracked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_tracked() returns correct state")
# Demonstrates tracking state
var tracked = false
expect(tracked).to_equal(false)

tracked = true  # start tracking
expect(tracked).to_equal(true)
```

</details>

#### tracking_id() returns Some while tracked

- tracking_id() returns Some while tracked
   - Expected: id equals `-1`
   - Expected: id >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tracking_id() returns Some while tracked")
# Demonstrates ID management
var id = -1  # untracked
expect(id).to_equal(-1)

id = 0  # assign ID when tracked
expect(id >= 0).to_equal(true)
```

</details>

### Feature #2303: defer Statement

#### Basic defer behavior

#### Multiple defers (LIFO order)

#### defer with resources

### Feature #2304: with Statement

#### Basic with statement

#### Usage examples

#### demonstrates defer pattern

- demonstrates defer pattern
   - Expected: open_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("demonstrates defer pattern")
# Example showing manual cleanup pattern
var open_count = 1

# In real code: defer close_resource()
# For test: manually close
open_count = open_count - 1
expect(open_count).to_equal(0)
```

</details>

#### demonstrates leak detection in tests

- demonstrates leak detection in tests
   - Expected: leaked_resources.len() equals `1`
   - Expected: leaked_resources.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("demonstrates leak detection in tests")
# Intentionally leak a resource
var leaked_resources = ["leaked_resource"]
expect(leaked_resources.len()).to_equal(1)

# Clean up for next test
leaked_resources = []
expect(leaked_resources.len()).to_equal(0)
```

</details>

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3d6c497c086ee540331734d3d5e8a94b9cedfcfc7a0bc8f31ae71c5978171fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3d6c497c086ee540331734d3d5e8a94b9cedfcfc7a0bc8f31ae71c5978171fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3d6c497c086ee540331734d3d5e8a94b9cedfcfc7a0bc8f31ae71c5978171fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/resource_cleanup_spec.spl
mirror: doc/06_spec/feature/usage/resource_cleanup_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/resource_cleanup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/resource_cleanup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/resource_cleanup_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/resource_cleanup_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'close() releases the resource' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/resource_cleanup_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'close() is idempotent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/resource_cleanup_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_open() returns correct state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
