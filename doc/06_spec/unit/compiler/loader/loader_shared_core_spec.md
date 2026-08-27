# Loader Shared Core Specification

> Tests covering Loader Shared-Core Refactor Invariants — AC-10.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader Shared Core Specification

## Scenarios

### Loader Shared-Core Refactor Invariants — AC-10

#### UnloadPolicy

#### empty policy is noop

- empty policy is noop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty policy is noop")
val p = UnloadPolicy.create("foo")
assert_true(p.is_noop())
```

</details>

#### policy with metadata not noop

- policy with metadata not noop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("policy with metadata not noop")
val p = UnloadPolicy.create("foo").with_metadata(3)
assert_false(p.is_noop())
```

</details>

#### metadata beats heuristic

- metadata beats heuristic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("metadata beats heuristic")
val p = UnloadPolicy.create("foo").with_metadata(2).with_heuristic(5)
assert_true(p.metadata_beats_heuristic())
```

</details>

#### heuristic only has no metadata priority

- heuristic only has no metadata priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("heuristic only has no metadata priority")
val p = UnloadPolicy.create("foo").with_heuristic(3)
assert_false(p.metadata_beats_heuristic())
```

</details>

#### InvariantCheck

#### unknown path noop passes

- unknown path noop passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown path noop passes")
val ic = InvariantCheck.unknown_path_noop(0)
assert_true(ic.passed)
```

</details>

#### unknown path noop fails

- unknown path noop fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown path noop fails")
val ic = InvariantCheck.unknown_path_noop(2)
assert_false(ic.passed)
```

</details>

#### metadata cleanup passes

- metadata cleanup passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("metadata cleanup passes")
val ic = InvariantCheck.metadata_cleanup(3, 5)
assert_true(ic.passed)
```

</details>

#### metadata priority with metadata

- metadata priority with metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("metadata priority with metadata")
val ic = InvariantCheck.metadata_priority(true, false)
assert_true(ic.passed)
```

</details>

#### metadata priority violated

- metadata priority violated


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("metadata priority violated")
val ic = InvariantCheck.metadata_priority(true, true)
assert_false(ic.passed)
```

</details>

#### MetadataEntry

#### belongs to its module path

- belongs to its module path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("belongs to its module path")
val e = MetadataEntry.create("sym_a", "mod.spl")
assert_true(e.belongs_to("mod.spl"))
```

</details>

#### does not belong to another path

- does not belong to another path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not belong to another path")
val e = MetadataEntry.create("sym_a", "mod.spl")
assert_false(e.belongs_to("other.spl"))
```

</details>

#### keeps its symbol name field

- keeps its symbol name field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps its symbol name field")
val e = MetadataEntry.create("mangled_foo", "path/bar.spl")
expect e.sym_name to eq "mangled_foo"
```

</details>

#### GlobalOwnership

#### is owned by its owner

- is owned by its owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is owned by its owner")
val g = GlobalOwnership.create("global_init", "main.spl")
assert_true(g.is_owned_by("main.spl"))
```

</details>

#### is not owned by another module

- is not owned by another module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not owned by another module")
val g = GlobalOwnership.create("global_init", "main.spl")
assert_false(g.is_owned_by("other.spl"))
```

</details>

#### JitState reload

#### tracked state is not resolvable

- tracked state is not resolvable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracked state is not resolvable")
val j = JitState.tracked("sym")
assert_false(j.is_resolvable())
```

</details>

#### resolvable after reload

- resolvable after reload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolvable after reload")
val j = JitState.tracked("sym").after_unload(true).after_reload(true)
assert_true(j.is_resolvable())
```

</details>

#### lost after unload without reload

- lost after unload without reload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lost after unload without reload")
val j = JitState.tracked("sym").after_unload(false).after_reload(false)
assert_false(j.is_resolvable())
```

</details>

#### Deterministic rebuild

#### passes when after == before - removed

- passes when after == before - removed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes when after == before - removed")
val ic = InvariantCheck.deterministic_rebuild(10, 3, 7)
assert_true(ic.passed)
```

</details>

#### fails when after != before - removed

- fails when after != before - removed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when after != before - removed")
val ic = InvariantCheck.deterministic_rebuild(10, 3, 8)
assert_false(ic.passed)
```

</details>

#### ScenarioResult

#### distinguishes pass from fail

- distinguishes pass from fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes pass from fail")
val p = ScenarioResult.pass_it("my_scenario", "all good")
val f = ScenarioResult.fail_it("my_scenario", "something broke")
assert_true(p.passed and (f.passed == false))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/loader/loader_shared_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Loader Shared-Core Refactor Invariants — AC-10.
- Loader Shared-Core Refactor Invariants — AC-10

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `48fa5856a4163b97f6d5a26c710d06d46c7e14f7c7200d015fe6841b54919163`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48fa5856a4163b97f6d5a26c710d06d46c7e14f7c7200d015fe6841b54919163`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48fa5856a4163b97f6d5a26c710d06d46c7e14f7c7200d015fe6841b54919163`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/loader/loader_shared_core_spec.spl
mirror: doc/06_spec/unit/compiler/loader/loader_shared_core_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/loader/loader_shared_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/loader/loader_shared_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/loader/loader_shared_core_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty policy is noop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/loader_shared_core_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'policy with metadata not noop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/loader/loader_shared_core_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'metadata beats heuristic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
