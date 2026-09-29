# scv_state_model_spec

> Purpose: This spec proves SCV-IMPL-G-03 — the v2 commit state model:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_state_model_spec

Purpose: This spec proves SCV-IMPL-G-03 — the v2 commit state model:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_state_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-G-03 — the v2 commit state model:
journal_only → private_editing/private_unparsed/private_parse_error/
private_parsed → compile_ok → test_ok → verified_ok → public_ready, with
transitions enforced (no skipping the chain, edits demote, forced_unparsed
never reaches public_ready), plus canonical mapping of legacy state names.
Audience: Maintainers of the SCV commit gates.

## Scenarios

### scv v2 state model (G-03)

#### accepts every canonical state and rejects junk

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
# @req REQ-SSPEC-INTEGRATION
for state in ["journal_only", "private_editing", "private_unparsed", "private_parse_error", "private_parsed", "forced_unparsed", "compile_ok", "test_ok", "verified_ok", "public_ready"]:
    expect(scv_state_model_valid(state)).to_be(true)
expect(scv_state_model_valid("")).to_be(false)
expect(scv_state_model_valid("green")).to_be(false)
expect(scv_state_model_valid("private_dirty")).to_be(false)
```

</details>

#### maps legacy state names onto the v2 model

- v2 names map to themselves; unknown names map to ERROR


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
expect(scv_state_canonical("private_dirty")).to_be("private_editing")
expect(scv_state_canonical("parsed_error")).to_be("private_parse_error")
expect(scv_state_canonical("parsed_ok")).to_be("private_parsed")
step("v2 names map to themselves; unknown names map to ERROR")
expect(scv_state_canonical("compile_ok")).to_be("compile_ok")
expect(scv_state_canonical("nonsense").starts_with("ERROR")).to_be(true)
```

</details>

#### orders the promotion chain by tier

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
expect(scv_state_tier("journal_only") < scv_state_tier("private_editing")).to_be(true)
expect(scv_state_tier("private_parsed") < scv_state_tier("compile_ok")).to_be(true)
expect(scv_state_tier("compile_ok") < scv_state_tier("test_ok")).to_be(true)
expect(scv_state_tier("test_ok") < scv_state_tier("verified_ok")).to_be(true)
expect(scv_state_tier("verified_ok") < scv_state_tier("public_ready")).to_be(true)
```

</details>

#### allows the forward chain one step at a time

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
expect(scv_state_transition_allowed("journal_only", "private_editing")).to_be(true)
expect(scv_state_transition_allowed("private_editing", "private_unparsed")).to_be(true)
expect(scv_state_transition_allowed("private_editing", "private_parse_error")).to_be(true)
expect(scv_state_transition_allowed("private_parse_error", "private_parsed")).to_be(true)
expect(scv_state_transition_allowed("private_parsed", "compile_ok")).to_be(true)
expect(scv_state_transition_allowed("compile_ok", "test_ok")).to_be(true)
expect(scv_state_transition_allowed("test_ok", "verified_ok")).to_be(true)
expect(scv_state_transition_allowed("verified_ok", "public_ready")).to_be(true)
```

</details>

#### refuses skipping the gate chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
expect(scv_state_transition_allowed("private_editing", "compile_ok")).to_be(false)
expect(scv_state_transition_allowed("private_parsed", "test_ok")).to_be(false)
expect(scv_state_transition_allowed("compile_ok", "verified_ok")).to_be(false)
expect(scv_state_transition_allowed("compile_ok", "public_ready")).to_be(false)
expect(scv_state_transition_allowed("test_ok", "public_ready")).to_be(false)
expect(scv_state_transition_allowed("journal_only", "public_ready")).to_be(false)
```

</details>

#### demotes on edit from any state, and never demotes below journal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
for state in ["private_unparsed", "private_parse_error", "private_parsed", "compile_ok", "test_ok", "verified_ok", "public_ready", "forced_unparsed"]:
    expect(scv_state_transition_allowed(state, "private_editing")).to_be(true)
expect(scv_state_transition_allowed("private_editing", "journal_only")).to_be(false)
expect(scv_state_transition_allowed("compile_ok", "private_parsed")).to_be(false)
```

</details>

#### never lets forced_unparsed reach public_ready (or the gate chain)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
expect(scv_state_transition_allowed("private_editing", "forced_unparsed")).to_be(true)
expect(scv_state_transition_allowed("forced_unparsed", "public_ready")).to_be(false)
expect(scv_state_transition_allowed("forced_unparsed", "compile_ok")).to_be(false)
expect(scv_state_transition_allowed("forced_unparsed", "test_ok")).to_be(false)
expect(scv_state_transition_allowed("forced_unparsed", "verified_ok")).to_be(false)
```

</details>

#### reports transitions with honest verdict text

- Legacy from-states are canonicalised before enforcement


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-STATE-MODEL-001
val ok = scv_state_transition("compile_ok", "test_ok")
expect(ok).to_contain("state: test_ok")
val bad = scv_state_transition("compile_ok", "public_ready")
expect(bad.starts_with("ERROR")).to_be(true)
val junk = scv_state_transition("compile_ok", "green")
expect(junk.starts_with("ERROR")).to_be(true)
step("Legacy from-states are canonicalised before enforcement")
val legacy = scv_state_transition("parsed_ok", "compile_ok")
expect(legacy).to_contain("state: compile_ok")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-STATE-MODEL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82f8fc8824c3138cbae4cafc066e99457ced5121ffba99d6f24295499928fed0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82f8fc8824c3138cbae4cafc066e99457ced5121ffba99d6f24295499928fed0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82f8fc8824c3138cbae4cafc066e99457ced5121ffba99d6f24295499928fed0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/scv_state_model_spec.spl
mirror: doc/06_spec/02_integration/app/scv_state_model_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_state_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_state_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_state_model_spec.spl:25:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts every canonical state and rejects junk' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_state_model_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps legacy state names onto the v2 model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_state_model_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'orders the promotion chain by tier' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_state_model_spec.spl:51:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'allows the forward chain one step at a time' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_state_model_spec.spl:62:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'refuses skipping the gate chain' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_state_model_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports transitions with honest verdict text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
