# Dependency Interface Digest in Cache Keys

> The gate is exercised here through its plain-data pair (`dep_iface_gate_record` / `dep_iface_gate_valid`) — the EXACT functions the BuildCache record/validate paths call — because the current self-hosted child test binary erases class values across module boundaries ("method/field not found on type `object`"; native_capsule_result_receipt_spec is red at HEAD for the same reason), so a BuildCache instance cannot be driven end-to-end from a spec. See doc/08_tracking/bug/selfhosted_child_erases_class_values_cross_module_2026-08-18.md.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dependency Interface Digest in Cache Keys

The gate is exercised here through its plain-data pair (`dep_iface_gate_record` / `dep_iface_gate_valid`) — the EXACT functions the BuildCache record/validate paths call — because the current self-hosted child test binary erases class values across module boundaries ("method/field not found on type `object`"; native_capsule_result_receipt_spec is red at HEAD for the same reason), so a BuildCache instance cannot be driven end-to-end from a spec. See doc/08_tracking/bug/selfhosted_child_erases_class_values_cross_module_2026-08-18.md.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/driver/dep_interface_cache_key_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The gate is exercised here through its plain-data pair
(`dep_iface_gate_record` / `dep_iface_gate_valid`) — the EXACT functions the
BuildCache record/validate paths call — because the current self-hosted child
test binary erases class values across module boundaries ("method/field not
found on type `object`"; native_capsule_result_receipt_spec is red at HEAD
for the same reason), so a BuildCache instance cannot be driven end-to-end
from a spec. See
doc/08_tracking/bug/selfhosted_child_erases_class_values_cross_module_2026-08-18.md.

Contract:
- a dependency's SIGNATURE edit changes the fold -> gate invalid;
- a dependency's BODY-only edit leaves the fold unchanged -> gate still
  valid (positive control: the gate cannot pass by invalidating everything);
- a missing/unreadable dependency, or an absent/corrupted recorded digest,
  fails CLOSED (never valid).

## Scenarios

### dependency_interface_fold (pure)

#### is deterministic and order-insensitive

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is deterministic and order-insensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is deterministic and order-insensitive")
val a = dependency_interface_fold(["p1=d1", "p2=d2"])
val b = dependency_interface_fold(["p2=d2", "p1=d1"])
assert_equal(a, b)
```

</details>

#### changes when any dependency digest changes

- changes when any dependency digest changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes when any dependency digest changes")
val a = dependency_interface_fold(["p1=d1", "p2=d2"])
val c = dependency_interface_fold(["p1=d1", "p2=OTHER"])
assert_true(a != c)
```

</details>

### interface-digest cache gate (record at compile, validate at reuse)

#### is valid when nothing changed since record time

- is valid when nothing changed since record time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is valid when nothing changed since record time")
val recorded = record_v1()
assert_true(dep_iface_gate_valid(recorded, [DEP_PATH, DEP2_PATH]))
```

</details>

#### stays valid after a dependency BODY-only edit (positive control)

- stays valid after a dependency BODY-only edit (positive control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays valid after a dependency BODY-only edit (positive control)")
val recorded = record_v1()
_ = file_write(DEP_PATH, DEP_BODY_EDIT)
assert_true(dep_iface_gate_valid(recorded, [DEP_PATH, DEP2_PATH]))
```

</details>

#### invalidates after a dependency INTERFACE edit

- invalidates after a dependency INTERFACE edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("invalidates after a dependency INTERFACE edit")
val recorded = record_v1()
_ = file_write(DEP_PATH, DEP_SIG_EDIT)
assert_false(dep_iface_gate_valid(recorded, [DEP_PATH, DEP2_PATH]))
```

</details>

#### fails closed when a dependency source is missing at validation

- fails closed when a dependency source is missing at validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed when a dependency source is missing at validation")
val recorded = record_v1()
_ = file_delete(DEP_PATH)
assert_false(dep_iface_gate_valid(recorded, [DEP_PATH, DEP2_PATH]))
```

</details>

#### fails closed on an absent/corrupted recorded digest

- fails closed on an absent/corrupted recorded digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed on an absent/corrupted recorded digest")
val recorded = record_v1()
# Sabotage: the recorded digest is blanked (legacy/corrupt entry
# shape) while every dependency is pristine on disk. Must NEVER
# validate — absent is not "unchanged".
assert_true(recorded != "")
assert_false(dep_iface_gate_valid("", [DEP_PATH, DEP2_PATH]))
```

</details>

#### records \

- records \


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records \")
_ = file_delete(DEP_PATH)
val recorded = dep_iface_gate_record([DEP_PATH, DEP2_PATH])
assert_equal(recorded, "")
assert_false(dep_iface_gate_valid(recorded, [DEP_PATH, DEP2_PATH]))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73a59e1725a41272198f37a23486ca991bead010fb17e5517edef2b3cbb8b6e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73a59e1725a41272198f37a23486ca991bead010fb17e5517edef2b3cbb8b6e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73a59e1725a41272198f37a23486ca991bead010fb17e5517edef2b3cbb8b6e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/dep_interface_cache_key_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/dep_interface_cache_key_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/dep_interface_cache_key_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/dep_interface_cache_key_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/dep_interface_cache_key_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is deterministic and order-insensitive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/dep_interface_cache_key_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'changes when any dependency digest changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/dep_interface_cache_key_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is valid when nothing changed since record time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
