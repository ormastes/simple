# Gui Native Model Specification

> Tests covering LLM Caret native GUI interaction model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gui Native Model Specification

## Scenarios

### LLM Caret native GUI interaction model

#### types lowercase prompt text from winit key codes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- types lowercase prompt text from winit key codes
   - Expected: state.prompt equals `test`
   - Expected: state.focused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("types lowercase prompt text from winit key codes")
var state = caret_native_state()
for key in [84, 69, 83, 84]:
    state = caret_native_key(state, key).state
expect(state.prompt).to_equal("test")
expect(state.focused).to_equal(true)
```

</details>

#### backspace edits and Enter emits a submit prompt

- backspace edits and Enter emits a submit prompt
   - Expected: state.prompt equals `a`
   - Expected: caret_native_key(state, 13).submit_prompt equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("backspace edits and Enter emits a submit prompt")
var state = caret_native_state()
state = caret_native_key(state, 65).state
state = caret_native_key(state, 66).state
state = caret_native_key(state, 8).state
expect(state.prompt).to_equal("a")
expect(caret_native_key(state, 13).submit_prompt).to_equal("a")
```

</details>

#### response application records a turn and resets the composer

- response application records a turn and resets the composer
   - Expected: final_state.prompt equals ``
   - Expected: final_state.user equals `test`
   - Expected: final_state.assistant equals `hello`
   - Expected: final_state.turn equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("response application records a turn and resets the composer")
var state = caret_native_state()
state = caret_native_key(state, 84).state
val final_state = caret_native_apply_response(state, "test", "hello")
expect(final_state.prompt).to_equal("")
expect(final_state.user).to_equal("test")
expect(final_state.assistant).to_equal("hello")
expect(final_state.turn).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/gui_native_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret native GUI interaction model.
- LLM Caret native GUI interaction model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2775979a30fa2f402890656a49f9d824ba79db28c5bbc69bec68e411fe43cd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2775979a30fa2f402890656a49f9d824ba79db28c5bbc69bec68e411fe43cd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2775979a30fa2f402890656a49f9d824ba79db28c5bbc69bec68e411fe43cd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/llm_caret/gui_native_model_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/gui_native_model_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/gui_native_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/gui_native_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/gui_native_model_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/gui_native_model_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'types lowercase prompt text from winit key codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/gui_native_model_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backspace edits and Enter emits a submit prompt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/gui_native_model_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'response application records a turn and resets the composer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
