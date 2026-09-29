# Joinpoint Patchpoint Specification

> Tests covering join-point slot table, AdviceBindingRegistry, join-point refusals (fail-closed).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Joinpoint Patchpoint Specification

## Scenarios

### join-point slot table

#### reserves a cell whose stable key is derived from owner, symbol and site

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reserves a cell whose stable key is derived from owner, symbol and site


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reserves a cell whose stable key is derived from owner, symbol and site")
val key = joinpoint_key("mod.a", "process", 3)
assert_eq(key, "mod.a::process#3")
# Same inputs must always give the same key -- the catalog routes on it.
assert_eq(key, joinpoint_key("mod.a", "process", 3))
assert_true(key != joinpoint_key("mod.a", "process", 4))
```

</details>

#### routes to the unadvised target by default

- routes to the unadvised target by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes to the unadvised target by default")
var table = ok_table(4)
val key = joinpoint_key("mod.a", "process", 0)
val slot = ok_i64(table.reserve(key, UNADVISED))
assert_eq(slot, 0)
_ = table.seal()
# Read straight out of the mapped page.
assert_eq(ok_i64(table.read_cell_raw(slot)), UNADVISED)
assert_eq(ok_i64(table.dispatch_target(slot)), UNADVISED)
_ = table.free()
```

</details>

#### patches one sealed cell without disturbing its neighbours

- patches one sealed cell without disturbing its neighbours


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("patches one sealed cell without disturbing its neighbours")
var table = ok_table(4)
val k0 = joinpoint_key("mod.a", "f", 0)
val k1 = joinpoint_key("mod.a", "g", 0)
val s0 = ok_i64(table.reserve(k0, UNADVISED))
val s1 = ok_i64(table.reserve(k1, UNADVISED))
_ = table.seal()
_ = table.patch_cell(s0, ADVICE_A)
assert_eq(ok_i64(table.read_cell_raw(s0)), ADVICE_A)
assert_eq(ok_i64(table.read_cell_raw(s1)), UNADVISED)
_ = table.free()
```

</details>

#### keeps the mapping executable after a patch (W^X round trip)

- keeps the mapping executable after a patch (W^X round trip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the mapping executable after a patch (W^X round trip)")
var table = ok_table(2)
val k = joinpoint_key("mod.a", "f", 0)
val s = ok_i64(table.reserve(k, UNADVISED))
_ = table.seal()
val before = table.protection_transitions
_ = table.patch_cell(s, ADVICE_A)
# A patch is exactly two transitions: RX->RW and RW->RX. An
# implementation that left the page RW would record one.
assert_eq(table.protection_transitions - before, 2)
_ = table.free()
```

</details>

### AdviceBindingRegistry

#### dispatches a registered join point to its unadvised target before any bind

- dispatches a registered join point to its unadvised target before any bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches a registered join point to its unadvised target before any bind")
var reg = ok_reg(4)
val key = ok_key(reg.register("mod.a", "process", 0, UNADVISED))
_ = reg.seal()
assert_eq(ok_i64(reg.dispatch_target(key)), UNADVISED)
assert_false(reg.is_active(key))
_ = reg.free()
```

</details>

#### routes the SAME join point to the advice after binding

- routes the SAME join point to the advice after binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes the SAME join point to the advice after binding")
var reg = ok_reg(4)
val key = ok_key(reg.register("mod.a", "process", 0, UNADVISED))
_ = reg.seal()
val slot_before = ok_i64(reg.slot_of(key))
assert_eq(ok_i64(reg.dispatch_target(key)), UNADVISED)

_ = reg.bind(key, ADVICE_A)

# Same key, same slot id -- the call SITE did not move; only its target.
assert_eq(ok_i64(reg.slot_of(key)), slot_before)
assert_eq(ok_i64(reg.dispatch_target(key)), ADVICE_A)
assert_true(reg.is_active(key))
_ = reg.free()
```

</details>

#### makes rebinding observable

- makes rebinding observable


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes rebinding observable")
var reg = ok_reg(4)
val key = ok_key(reg.register("mod.a", "process", 0, UNADVISED))
_ = reg.seal()
_ = reg.bind(key, ADVICE_A)
assert_eq(reg.rebind_count(key), 1)
_ = reg.bind(key, ADVICE_B)
assert_eq(ok_i64(reg.dispatch_target(key)), ADVICE_B)
assert_eq(reg.rebind_count(key), 2)
# Unbind restores the unadvised target -- it is a restore, not a reset.
assert_eq(ok_i64(reg.unbind(key)), UNADVISED)
assert_eq(ok_i64(reg.dispatch_target(key)), UNADVISED)
assert_false(reg.is_active(key))
assert_eq(reg.rebind_count(key), 3)
_ = reg.free()
```

</details>

### join-point refusals (fail-closed)

#### refuses an out-of-range slot id instead of silently ignoring it

- refuses an out-of-range slot id instead of silently ignoring it


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an out-of-range slot id instead of silently ignoring it")
var table = ok_table(4)
val s = ok_i64(table.reserve(joinpoint_key("m", "f", 0), UNADVISED))
_ = table.seal()
assert_true(is_err_i64(table.patch_cell(99, ADVICE_A)))
assert_true(is_err_i64(table.patch_cell(-1, ADVICE_A)))
# `capacity` is 4 but only 1 slot is USED -- an unreserved in-capacity
# id must still be refused.
assert_true(is_err_i64(table.patch_cell(2, ADVICE_A)))
assert_true(is_err_i64(table.dispatch_target(2)))
# The one real slot is untouched by all of that.
assert_eq(ok_i64(table.read_cell_raw(s)), UNADVISED)
_ = table.free()
```

</details>

#### refuses an unknown join-point key instead of defaulting

- refuses an unknown join-point key instead of defaulting


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an unknown join-point key instead of defaulting")
var reg = ok_reg(4)
_ = reg.register("mod.a", "process", 0, UNADVISED)
_ = reg.seal()
val ghost = joinpoint_key("mod.a", "nosuch", 0)
assert_true(is_err_i64(reg.slot_of(ghost)))
assert_true(is_err_i64(reg.dispatch_target(ghost)))
assert_true(is_err_i64(reg.bind(ghost, ADVICE_A)))
assert_true(is_err_i64(reg.unbind(ghost)))
assert_contains(err_text(reg.bind(ghost, ADVICE_A)), "unregistered")
_ = reg.free()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/joinpoint_patchpoint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering join-point slot table, AdviceBindingRegistry, join-point refusals (fail-closed).
- join-point slot table
- AdviceBindingRegistry
- join-point refusals (fail-closed)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `ed0015d8ffbec295c0d0021166a6213244079809443a56ff9d9532758a2255aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed0015d8ffbec295c0d0021166a6213244079809443a56ff9d9532758a2255aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed0015d8ffbec295c0d0021166a6213244079809443a56ff9d9532758a2255aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/loader/joinpoint_patchpoint_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/joinpoint_patchpoint_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/joinpoint_patchpoint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/joinpoint_patchpoint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/joinpoint_patchpoint_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reserves a cell whose stable key is derived from owner, symbol and site' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/joinpoint_patchpoint_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes to the unadvised target by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/joinpoint_patchpoint_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'patches one sealed cell without disturbing its neighbours' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
