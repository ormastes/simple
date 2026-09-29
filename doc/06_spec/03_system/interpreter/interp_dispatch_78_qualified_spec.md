# Interp Dispatch 78 Qualified Specification

> Tests covering Module-qualified dispatch (task 78), Module-qualified dispatch collision probe (task 78).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Dispatch 78 Qualified Specification

## Scenarios

### Module-qualified dispatch (task 78)

#### constructs a struct via module-qualified call

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs a struct via module-qualified call


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constructs a struct via module-qualified call")
val v = math.Vec3Math78(x: 1, y: 2, z: 3)
expect v.x == 1
expect v.y == 2
expect v.z == 3
```

</details>

#### calls a free function via module-qualified call

- calls a free function via module-qualified call


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls a free function via module-qualified call")
val a = math.Vec3Math78(x: 1, y: 2, z: 3)
val b = math.Vec3Math78(x: 10, y: 20, z: 30)
val c = math.add_vec3_78(a, b)
expect c.x == 11
expect c.y == 22
expect c.z == 33
```

</details>

### Module-qualified dispatch collision probe (task 78)

#### constructs vmath.Vec3 while a locally-named Vec3 struct also exists

- constructs vmath.Vec3 while a locally-named Vec3 struct also exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constructs vmath.Vec3 while a locally-named Vec3 struct also exists")
val local_v = Vec3(a: 100, b: 200)
val remote_v = vmath.Vec3(x: 1, y: 2, z: 3)
expect local_v.a == 100
expect remote_v.x == 1
expect remote_v.y == 2
expect remote_v.z == 3
```

</details>

#### calls vmath.make_vec3 while a locally-named Vec3 struct also exists

- calls vmath.make_vec3 while a locally-named Vec3 struct also exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls vmath.make_vec3 while a locally-named Vec3 struct also exists")
val remote_v = vmath.make_vec3(7, 8, 9)
expect remote_v.x == 7
expect remote_v.z == 9
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/interp_dispatch_78_qualified_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module-qualified dispatch (task 78), Module-qualified dispatch collision probe (task 78).
- Module-qualified dispatch (task 78)
- Module-qualified dispatch collision probe (task 78)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `2f7070660bbccf5f3ae7f945c52639de6fc454ba992d6551031da038741d2bd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f7070660bbccf5f3ae7f945c52639de6fc454ba992d6551031da038741d2bd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f7070660bbccf5f3ae7f945c52639de6fc454ba992d6551031da038741d2bd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/interpreter/interp_dispatch_78_qualified_spec.spl
mirror: doc/06_spec/03_system/interpreter/interp_dispatch_78_qualified_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/interpreter/interp_dispatch_78_qualified_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/interpreter/interp_dispatch_78_qualified_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/interpreter/interp_dispatch_78_qualified_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a struct via module-qualified call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/interp_dispatch_78_qualified_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a free function via module-qualified call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/interp_dispatch_78_qualified_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs vmath.Vec3 while a locally-named Vec3 struct also exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
