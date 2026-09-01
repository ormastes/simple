# Env Nullable Lookup Family Detection Specification

> Tests covering nullable env-lookup family — dead-fallback detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Env Nullable Lookup Family Detection Specification

## Scenarios

### nullable env-lookup family — dead-fallback detection

#### every nullable accessor lets ?? reach the default for every unset key

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- every nullable accessor lets ?? reach the default for every unset key
   - Expected: env_get_opt(key) ?? "SENTINEL" equals `SENTINEL`
   - Expected: env_get_or(key, "SENTINEL") equals `SENTINEL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every nullable accessor lets ?? reach the default for every unset key")
for key in UNSET_KEYS:
    expect(env_get_opt(key) ?? "SENTINEL").to_equal("SENTINEL")
    expect(env_get_or(key, "SENTINEL")).to_equal("SENTINEL")
```

</details>

#### no nullable accessor takes the default when a value is present

- no nullable accessor takes the default when a value is present
   - Expected: ok is true
   - Expected: env_get_opt(key + "_LIVE") ?? "SENTINEL" equals `"value" + i.to_text()`
   - Expected: env_get_or(key + "_LIVE", "SENTINEL") equals `"value" + i.to_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no nullable accessor takes the default when a value is present")
# A `?? default` that fires unconditionally is the same silent class of
# wrong answer as one that never fires.
var i = 0
for key in UNSET_KEYS:
    val ok = env_set(key + "_LIVE", "value" + i.to_text())
    expect(ok).to_equal(true)
    expect(env_get_opt(key + "_LIVE") ?? "SENTINEL").to_equal("value" + i.to_text())
    expect(env_get_or(key + "_LIVE", "SENTINEL")).to_equal("value" + i.to_text())
    i = i + 1
```

</details>

#### the known non-nullable accessor keeps its documented sentinel

- the known non-nullable accessor keeps its documented sentinel
   - Expected: env_get(key) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the known non-nullable accessor keeps its documented sentinel")
# Pinned deliberately: `env_get` returning "" is WHY `?? default` is dead
# there. If this flips, every `env_get(k) ?? d` site changes meaning and
# that must break loudly here rather than silently in production.
for key in UNSET_KEYS:
    expect(env_get(key)).to_equal("")
```

</details>

#### the invariants hold on the run path, not only in the interpreter

- the invariants hold on the run path, not only in the interpreter
   - Expected: out contains `PROBE_VERDICT=PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the invariants hold on the run path, not only in the interpreter")
val out = run_probe()
expect(out.contains("PROBE_VERDICT=PASS")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nullable env-lookup family — dead-fallback detection.
- nullable env-lookup family — dead-fallback detection

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4592f146f9686d402d4e0b137e82f539562ed12ad3a265b87bb94f0b0db7016`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4592f146f9686d402d4e0b137e82f539562ed12ad3a265b87bb94f0b0db7016`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4592f146f9686d402d4e0b137e82f539562ed12ad3a265b87bb94f0b0db7016`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'every nullable accessor lets ?? reach the default for every unset key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no nullable accessor takes the default when a value is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/env_nullable_lookup_family_detection_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the known non-nullable accessor keeps its documented sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
