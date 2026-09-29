# Env Get Nil Coalesce Fallback Specification

> Tests covering env_get nil-coalesce fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Env Get Nil Coalesce Fallback Specification

## Scenarios

### env_get nil-coalesce fallback

#### env_get on an unset key yields the empty string, not nil

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- env_get on an unset key yields the empty string, not nil
   - Expected: env_get(UNSET_KEY) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_get on an unset key yields the empty string, not nil")
# This is the defect itself, pinned so a future change to env_get's
# return type shows up here as an intentional break rather than silently.
expect(env_get(UNSET_KEY)).to_equal("")
```

</details>

#### env_get_opt on an unset key lets ?? take the default

- env_get_opt on an unset key lets ?? take the default
   - Expected: env_get_opt(UNSET_KEY) ?? "FALLBACK" equals `FALLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_get_opt on an unset key lets ?? take the default")
expect(env_get_opt(UNSET_KEY) ?? "FALLBACK").to_equal("FALLBACK")
```

</details>

#### env_get_or on an unset key returns the default

- env_get_or on an unset key returns the default
   - Expected: env_get_or(UNSET_KEY, "FALLBACK") equals `FALLBACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_get_or on an unset key returns the default")
expect(env_get_or(UNSET_KEY, "FALLBACK")).to_equal("FALLBACK")
```

</details>

#### env_get_opt on a set key returns the live value, not the default

- env_get_opt on a set key returns the live value, not the default
   - Expected: ok is true
   - Expected: env_get_opt(SET_KEY) ?? "FALLBACK" equals `live-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_get_opt on a set key returns the live value, not the default")
val ok = env_set(SET_KEY, "live-value")
expect(ok).to_equal(true)
expect(env_get_opt(SET_KEY) ?? "FALLBACK").to_equal("live-value")
```

</details>

#### env_get_or on a set key returns the live value, not the default

- env_get_or on a set key returns the live value, not the default
   - Expected: ok is true
   - Expected: env_get_or(SET_KEY, "FALLBACK") equals `live-value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env_get_or on a set key returns the live value, not the default")
val ok = env_set(SET_KEY, "live-value")
expect(ok).to_equal(true)
expect(env_get_or(SET_KEY, "FALLBACK")).to_equal("live-value")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering env_get nil-coalesce fallback.
- env_get nil-coalesce fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `0ee1bd53561c729679e4428a9b45b4dcc477121eaf16f5094120423c008919ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ee1bd53561c729679e4428a9b45b4dcc477121eaf16f5094120423c008919ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ee1bd53561c729679e4428a9b45b4dcc477121eaf16f5094120423c008919ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_get on an unset key yields the empty string, not nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_get_opt on an unset key lets ?? take the default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/env_get_nil_coalesce_fallback_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_get_or on an unset key returns the default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
