# Marker Wire Format Specification

> Tests covering markers.find_spec strict prefix matching, validate() rejects level-prefixed markers, log_level_name composition (log_info wire format), namespace_prefix / marker_string round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Marker Wire Format Specification

## Scenarios

### markers.find_spec strict prefix matching

#### matches a bare '[BOOT] entry' marker

- matches a bare '[BOOT] entry' marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches a bare '[BOOT] entry' marker")
val raw = "[BOOT] entry"
val spec = find_spec(raw)
expect(spec).to_not_be_nil()
```

</details>

#### does NOT match '[INFO] [BOOT] entry' (the regression shape)

- does NOT match '[INFO] [BOOT] entry' (the regression shape)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT match '[INFO] [BOOT] entry' (the regression shape)")
val raw_with_level = "[INFO] [BOOT] entry"
val spec = find_spec(raw_with_level)
expect(spec).to_be_nil()
```

</details>

#### rejects unknown namespace prefixes

- rejects unknown namespace prefixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown namespace prefixes")
val raw = "[nonsense] event"
val spec = find_spec(raw)
expect(spec).to_be_nil()
```

</details>

### validate() rejects level-prefixed markers

#### validates a bare marker

- validates a bare marker
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates a bare marker")
val result = validate("[BOOT] entry")
expect(result.is_ok()).to_equal(true)
```

</details>

#### rejects the same marker with an [INFO] prefix

- rejects the same marker with an [INFO] prefix
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the same marker with an [INFO] prefix")
val result = validate("[INFO] [BOOT] entry")
expect(result.is_ok()).to_equal(false)
```

</details>

### log_level_name composition (log_info wire format)

#### INFO prefix is exactly '[INFO]'

- INFO prefix is exactly '[INFO]'
   - Expected: level_token equals `[INFO]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("INFO prefix is exactly '[INFO]'")
val level_token = "[" + log_level_name(LOG_INFO) + "]"
expect(level_token).to_equal("[INFO]")
```

</details>

### namespace_prefix / marker_string round-trip

#### marker_string for boot namespace produces '[BOOT] event'

- marker_string for boot namespace produces '[BOOT] event'
   - Expected: s.starts_with(namespace_prefix(MarkerNamespace.Boot) + " ") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marker_string for boot namespace produces '[BOOT] event'")
val s = marker_string(MarkerNamespace.Boot, "entry")
expect(s.starts_with(namespace_prefix(MarkerNamespace.Boot) + " ")).to_equal(true)
```

</details>

#### the produced marker is accepted by find_spec

- the produced marker is accepted by find_spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the produced marker is accepted by find_spec")
val s = marker_string(MarkerNamespace.Boot, "entry")
val spec = find_spec(s)
expect(spec).to_not_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/logging/marker_wire_format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering markers.find_spec strict prefix matching, validate() rejects level-prefixed markers, log_level_name composition (log_info wire format), namespace_prefix / marker_string round-trip.
- markers.find_spec strict prefix matching
- validate() rejects level-prefixed markers
- log_level_name composition (log_info wire format)
- namespace_prefix / marker_string round-trip

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9f91a20aea1c7f8e31fef8bb96694299fa3840d486ab8cacc6a37489e98956ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f91a20aea1c7f8e31fef8bb96694299fa3840d486ab8cacc6a37489e98956ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f91a20aea1c7f8e31fef8bb96694299fa3840d486ab8cacc6a37489e98956ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/logging/marker_wire_format_spec.spl
mirror: doc/06_spec/unit/os/kernel/logging/marker_wire_format_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/logging/marker_wire_format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/logging/marker_wire_format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/logging/marker_wire_format_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches a bare '[BOOT] entry' marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/logging/marker_wire_format_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT match '[INFO] [BOOT] entry' (the regression shape)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/logging/marker_wire_format_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown namespace prefixes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
