# Effects Specification

> Tests covering EffectTag and EffectEnv.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effects Specification

## Scenarios

### EffectTag and EffectEnv

#### propagates suspension through tag combination in both orders

**Manual warnings:**
- invalid manual visibility metadata: # @manual effect inference evidence (expected show, folded, detail, or skip)


- combine pure and suspending tags in both argument orders
   - Expected: EffectTag.PureTag.combine(EffectTag.SuspendingTag).to_string() equals `async`
   - Expected: EffectTag.SuspendingTag.combine(EffectTag.PureTag).to_string() equals `async`
   - Expected: EffectTag.PureTag.combine(EffectTag.PureTag).to_string() equals `sync`
- fold a tag list with combine_all


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combine pure and suspending tags in both argument orders")
expect(EffectTag.PureTag.combine(EffectTag.SuspendingTag).to_string()).to_equal("async")
expect(EffectTag.SuspendingTag.combine(EffectTag.PureTag).to_string()).to_equal("async")
expect(EffectTag.PureTag.combine(EffectTag.PureTag).to_string()).to_equal("sync")
step("fold a tag list with combine_all")
expect(EffectTag.combine_all(
    [EffectTag.PureTag, EffectTag.SuspendingTag, EffectTag.PureTag]
).to_string()).to_equal("async")
expect(EffectTag.combine_all(
    [EffectTag.PureTag, EffectTag.PureTag]
).to_string()).to_equal("sync")
```

</details>

#### resolves builtin SFFI effects and defaults unknown symbols to sync

- query the builtin effect table through a fresh EffectEnv
   - Expected: env.get_effect("http.get").to_string() equals `async`
   - Expected: env.get_effect("no.such.builtin.symbol").to_string() equals `sync`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query the builtin effect table through a fresh EffectEnv")
val env = EffectEnv.new()
# oracle: http.get is annotated async in init_builtins (network I/O)
expect(env.get_effect("http.get").to_string()).to_equal("async")
expect(env.get_effect("no.such.builtin.symbol").to_string()).to_equal("sync")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/common/effects_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering EffectTag and EffectEnv.
- EffectTag and EffectEnv

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `58c6feea2db2eab8697874dfcb3192d679e73d33cba174514543efc97f6df672`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58c6feea2db2eab8697874dfcb3192d679e73d33cba174514543efc97f6df672`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58c6feea2db2eab8697874dfcb3192d679e73d33cba174514543efc97f6df672`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/unit/compiler/common/effects_spec.spl
mirror: doc/06_spec/unit/compiler/common/effects_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/common/effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/common/effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/common/effects_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates suspension through tag combination in both orders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/effects_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves builtin SFFI effects and defaults unknown symbols to sync' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
