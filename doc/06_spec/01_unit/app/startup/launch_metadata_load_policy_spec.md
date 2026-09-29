# Launch Metadata Load Policy Specification

> Tests covering load_policy value set, default load_policy per artifact kind, mmap_hint compat mapping, unknown load_policy fails closed, plan carries the resolved policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launch Metadata Load Policy Specification

## Scenarios

### load_policy value set

#### accepts exactly the six declared policies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts exactly the six declared policies


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts exactly the six declared policies")
assert_true(load_policy_is_valid(LOAD_POLICY_NORMAL))
assert_true(load_policy_is_valid(LOAD_POLICY_INDEX_ONLY))
assert_true(load_policy_is_valid(LOAD_POLICY_MAP_SELECTED_SEGMENTS))
assert_true(load_policy_is_valid(LOAD_POLICY_READ_AHEAD_SELECTED))
assert_true(load_policy_is_valid(LOAD_POLICY_DIRECT_EXEC))
assert_true(load_policy_is_valid(LOAD_POLICY_AUTO))
```

</details>

#### rejects unknown and sentinel values

- rejects unknown and sentinel values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown and sentinel values")
assert_false(load_policy_is_valid("turbo"))
assert_false(load_policy_is_valid(""))
assert_false(load_policy_is_valid(LOAD_POLICY_INVALID))
```

</details>

### default load_policy per artifact kind

#### defaults scripts and smf to map_selected_segments

- defaults scripts and smf to map_selected_segments
   - Expected: script_meta.load_policy equals `LOAD_POLICY_MAP_SELECTED_SEGMENTS`
   - Expected: smf_meta.load_policy equals `LOAD_POLICY_MAP_SELECTED_SEGMENTS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults scripts and smf to map_selected_segments")
val script_meta = launch_metadata_default("script")
val smf_meta = launch_metadata_default("smf")
expect(script_meta.load_policy).to_equal(LOAD_POLICY_MAP_SELECTED_SEGMENTS)
expect(smf_meta.load_policy).to_equal(LOAD_POLICY_MAP_SELECTED_SEGMENTS)
assert_true(script_meta.mmap_hint)
```

</details>

#### defaults native builds to normal

- defaults native builds to normal
   - Expected: native_meta.load_policy equals `LOAD_POLICY_NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults native builds to normal")
val native_meta = launch_metadata_for_native_build("linux", "x86_64", "gnu")
expect(native_meta.load_policy).to_equal(LOAD_POLICY_NORMAL)
assert_false(native_meta.mmap_hint)
```

</details>

#### defaults simpleos paths to map_selected_segments

- defaults simpleos paths to map_selected_segments
   - Expected: meta.load_policy equals `LOAD_POLICY_MAP_SELECTED_SEGMENTS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults simpleos paths to map_selected_segments")
val meta = launch_metadata_for_simpleos_path("app.smf")
expect(meta.load_policy).to_equal(LOAD_POLICY_MAP_SELECTED_SEGMENTS)
```

</details>

### mmap_hint compat mapping

#### maps legacy mmap_hint to load_policy old-to-new

- maps legacy mmap_hint to load_policy old-to-new
   - Expected: load_policy_from_mmap_hint(true) equals `LOAD_POLICY_MAP_SELECTED_SEGMENTS`
   - Expected: load_policy_from_mmap_hint(false) equals `LOAD_POLICY_NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps legacy mmap_hint to load_policy old-to-new")
expect(load_policy_from_mmap_hint(true)).to_equal(LOAD_POLICY_MAP_SELECTED_SEGMENTS)
expect(load_policy_from_mmap_hint(false)).to_equal(LOAD_POLICY_NORMAL)
```

</details>

#### derives legacy mmap_hint from load_policy new-to-old

- derives legacy mmap_hint from load_policy new-to-old


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives legacy mmap_hint from load_policy new-to-old")
assert_true(load_policy_implies_mmap_hint(LOAD_POLICY_MAP_SELECTED_SEGMENTS))
assert_true(load_policy_implies_mmap_hint(LOAD_POLICY_READ_AHEAD_SELECTED))
assert_true(load_policy_implies_mmap_hint(LOAD_POLICY_AUTO))
assert_false(load_policy_implies_mmap_hint(LOAD_POLICY_NORMAL))
assert_false(load_policy_implies_mmap_hint(LOAD_POLICY_DIRECT_EXEC))
```

</details>

#### decodes a pre-policy sidecar via mmap_hint

- decodes a pre-policy sidecar via mmap_hint
   - Expected: meta.load_policy equals `LOAD_POLICY_MAP_SELECTED_SEGMENTS`
   - Expected: meta_off.load_policy equals `LOAD_POLICY_NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a pre-policy sidecar via mmap_hint")
val legacy = "simple_launch_metadata:\n  entry_kind: \"native\"\n  mmap_hint: true\n"
val meta = parse_launch_metadata_sidecar(legacy, "native")
expect(meta.load_policy).to_equal(LOAD_POLICY_MAP_SELECTED_SEGMENTS)
val legacy_off = "simple_launch_metadata:\n  entry_kind: \"native\"\n  mmap_hint: false\n"
val meta_off = parse_launch_metadata_sidecar(legacy_off, "native")
expect(meta_off.load_policy).to_equal(LOAD_POLICY_NORMAL)
```

</details>

#### lets an explicit load_policy win over the legacy hint and re-derives it

- lets an explicit load_policy win over the legacy hint and re-derives it
   - Expected: meta.load_policy equals `LOAD_POLICY_NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets an explicit load_policy win over the legacy hint and re-derives it")
val content = "simple_launch_metadata:\n  mmap_hint: true\n  load_policy: \"normal\"\n"
val meta = parse_launch_metadata_sidecar(content, "script")
expect(meta.load_policy).to_equal(LOAD_POLICY_NORMAL)
assert_false(meta.mmap_hint)
```

</details>

#### round-trips load_policy through the sidecar text

- round-trips load_policy through the sidecar text
   - Expected: parsed.load_policy equals `LOAD_POLICY_READ_AHEAD_SELECTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips load_policy through the sidecar text")
var meta = launch_metadata_default("script")
meta.load_policy = LOAD_POLICY_READ_AHEAD_SELECTED
val rendered = render_launch_metadata_sidecar(meta)
val parsed = parse_launch_metadata_sidecar(rendered, "script")
expect(parsed.load_policy).to_equal(LOAD_POLICY_READ_AHEAD_SELECTED)
assert_true(parsed.mmap_hint)
```

</details>

#### plans the alias and the mapped policy identically

- plans the alias and the mapped policy identically
   - Expected: startup_feature_summary(alias_plan) equals `startup_feature_summary(mapped_plan)`
   - Expected: alias_plan.load_policy equals `LOAD_POLICY_MAP_SELECTED_SEGMENTS`
   - Expected: alias_plan.cache_strategy equals `mmap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans the alias and the mapped policy identically")
var alias_meta = launch_metadata_default("script")
alias_meta.load_policy = LOAD_POLICY_AUTO
var mapped_meta = launch_metadata_default("script")
mapped_meta.load_policy = LOAD_POLICY_MAP_SELECTED_SEGMENTS
val alias_plan = startup_plan_from_metadata("a.spl", [], alias_meta, true, false)
val mapped_plan = startup_plan_from_metadata("a.spl", [], mapped_meta, true, false)
expect(startup_feature_summary(alias_plan)).to_equal(startup_feature_summary(mapped_plan))
expect(alias_plan.load_policy).to_equal(LOAD_POLICY_MAP_SELECTED_SEGMENTS)
expect(alias_plan.cache_strategy).to_equal("mmap")
```

</details>

### unknown load_policy fails closed

#### parses an unknown declared policy to the invalid sentinel

- parses an unknown declared policy to the invalid sentinel
   - Expected: meta.load_policy equals `LOAD_POLICY_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses an unknown declared policy to the invalid sentinel")
val content = "simple_launch_metadata:\n  load_policy: \"turbo\"\n"
val meta = parse_launch_metadata_sidecar(content, "script")
expect(meta.load_policy).to_equal(LOAD_POLICY_INVALID)
```

</details>

#### refuses to build a supported plan from an invalid policy

- refuses to build a supported plan from an invalid policy
   - Expected: plan.load_policy equals `LOAD_POLICY_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to build a supported plan from an invalid policy")
val content = "simple_launch_metadata:\n  load_policy: \"turbo\"\n"
val meta = parse_launch_metadata_sidecar(content, "script")
val plan = startup_plan_from_metadata("a.spl", [], meta, true, true)
assert_false(plan.supported)
expect(plan.load_policy).to_equal(LOAD_POLICY_INVALID)
assert_false(plan.include_mmap_cache)
assert_true(plan.error.len() > 0)
```

</details>

### plan carries the resolved policy

#### resolves normal policy to a normal_read strategy

- resolves normal policy to a normal_read strategy
   - Expected: plan.load_policy equals `LOAD_POLICY_NORMAL`
   - Expected: plan.cache_strategy equals `normal_read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves normal policy to a normal_read strategy")
val meta = launch_metadata_for_native_build("linux", "x86_64", "gnu")
val plan = startup_plan_from_metadata("app", [], meta, true, true)
expect(plan.load_policy).to_equal(LOAD_POLICY_NORMAL)
expect(plan.cache_strategy).to_equal("normal_read")
assert_true(plan.supported)
```

</details>

#### resolves effective policy for empty legacy metadata fields

- resolves effective policy for empty legacy metadata fields
   - Expected: launch_metadata_effective_load_policy(meta) equals `LOAD_POLICY_MAP_SELECTED_SEGMENTS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves effective policy for empty legacy metadata fields")
var meta = launch_metadata_default("script")
meta.load_policy = ""
expect(launch_metadata_effective_load_policy(meta)).to_equal(LOAD_POLICY_MAP_SELECTED_SEGMENTS)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/launch_metadata_load_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering load_policy value set, default load_policy per artifact kind, mmap_hint compat mapping, unknown load_policy fails closed, plan carries the resolved policy.
- load_policy value set
- default load_policy per artifact kind
- mmap_hint compat mapping
- unknown load_policy fails closed
- plan carries the resolved policy

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

- Canonical SPipe generation for source `0fb78cf9cca4cd3004cf721e93bb410efdf1ec36a1735757db75793bead9d1a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0fb78cf9cca4cd3004cf721e93bb410efdf1ec36a1735757db75793bead9d1a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0fb78cf9cca4cd3004cf721e93bb410efdf1ec36a1735757db75793bead9d1a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/launch_metadata_load_policy_spec.spl
mirror: doc/06_spec/01_unit/app/startup/launch_metadata_load_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/launch_metadata_load_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/launch_metadata_load_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/launch_metadata_load_policy_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts exactly the six declared policies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/launch_metadata_load_policy_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown and sentinel values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/launch_metadata_load_policy_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults scripts and smf to map_selected_segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
