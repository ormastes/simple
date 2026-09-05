# Database Feature Utils Specification

> Tests covering Database Feature Utils, My Feature, Auto ID Feature.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Feature Utils Specification

## Scenarios

### Database Feature Utils

#### parses attribute lists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses attribute lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses attribute lists")
val modes = parse_attr_list("modes(\"pure\", \"hybrid\")", "modes")
check(modes.len() == 2)
check(modes[0] == "pure")
check(modes[1] == "hybrid")
```

</details>

#### extracts quoted names

- extracts quoted names


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts quoted names")
check(extract_quoted_string("describe \"My Feature\":") == "My Feature")
```

</details>

#### extracts categories from feature paths

- extracts categories from feature paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts categories from feature paths")
check(extract_category_from_path("test/system/features/control_flow/loops_spec.spl") == "control_flow")
check(extract_category_from_path("spec.spl") == "uncategorized")
```

</details>

#### compares feature ids semantically

- compares feature ids semantically


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares feature ids semantically")
check(compare_feature_id("1.2", "1.10") < 0)
check(compare_feature_id("1.10.1", "1.2.20") > 0)
check(compare_feature_id("alpha", "beta") < 0)
```

</details>

#### parses spipe metadata from a temp file

- parses spipe metadata from a temp file


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses spipe metadata from a temp file")
val path = write_spec("metadata", """
```

</details>

### My Feature

### Auto ID Feature

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | feature_001 |
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_feature_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Database Feature Utils, My Feature, Auto ID Feature.
- Database Feature Utils
- My Feature
- Auto ID Feature

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `3b25f7503f4db3e43d7a51cc4c3bdad6a1c1b1ce06b897146abc0ba677302eca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b25f7503f4db3e43d7a51cc4c3bdad6a1c1b1ce06b897146abc0ba677302eca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b25f7503f4db3e43d7a51cc4c3bdad6a1c1b1ce06b897146abc0ba677302eca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/database/database_feature_utils_spec.spl
mirror: doc/06_spec/01_unit/lib/database/database_feature_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/database_feature_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/database_feature_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/database_feature_utils_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses attribute lists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/database_feature_utils_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts quoted names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/database_feature_utils_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts categories from feature paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
