# Canceled Browser Text Editing

> This specification proves hosted and isolated-worker text controls preserve the same UTF-8 selection when cancelable `beforeinput` blocks Backspace or Delete. Both routes use the canonical BrowserSession DOM event and editing owners.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Canceled Browser Text Editing

This specification proves hosted and isolated-worker text controls preserve the same UTF-8 selection when cancelable `beforeinput` blocks Backspace or Delete. Both routes use the canonical BrowserSession DOM event and editing owners.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/04_architecture/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification proves hosted and isolated-worker text controls preserve the
same UTF-8 selection when cancelable `beforeinput` blocks Backspace or Delete.
Both routes use the canonical BrowserSession DOM event and editing owners.

## Requirements

**Requirements:** doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md

- REQ-WEB-BROWSER-007: cancellation must suppress the default edit without
  corrupting live selection state.
- REQ-WEB-BROWSER-008: keyboard editing, `beforeinput`, `input`, `change`,
  selection movement, and blur must agree across hosted and worker paths.

## Plan

**Plan:** doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md

## Design

**Design:** doc/04_architecture/simple_web_browser_engine_production_hardening.md

## Research

**Research:** doc/01_research/local/simple_web_browser_engine_production_hardening.md

Domain context: `doc/01_research/domain/simple_web_browser_engine_production_hardening.md`

## Behavior and UTF-8 Example

The fixture value is `aéz`. Its selected `é` occupies UTF-8 byte range `1..3`.
Canceled Backspace and Delete must leave the value and selection unchanged.
The observable order is `keydown` then canceled `beforeinput`; neither `input`
nor `change` may follow. Shift+ArrowRight must then extend focus from byte 3 to
byte 4, proving the retained selection was used. Blur finally clears the
selection target and resets both byte offsets to zero.

## Examples

Given the value and byte boundaries:

```text
value:  a é   z
bytes:  0 1-2 3
range:    [1,3)
```

the canceling listener produces this transition:

```text
selection 1..3
  -> keydown Backspace
  -> beforeinput preventDefault()
  -> value remains aéz
  -> selection remains 1..3
```

The next shifted cursor operation proves cancellation retained both ends:

```text
Shift+ArrowRight
  -> anchor remains 1
  -> focus advances from 3 to 4
```

## Host and Worker Parity

The hosted case calls the public input surface used by an in-process Web
window. The worker case sends the unchanged K2 keyboard message through the
isolated renderer session. Both end with identical DOM value, selection,
event title, and blur cleanup.

No test-only editing path is introduced. A difference between these rows means
the hosted adapter or worker IPC adapter bypassed the canonical BrowserSession
default-action owner.

## Failure Discrimination

The assertions distinguish the original bug from nearby failures:

- A changed value means cancellation did not suppress the edit.
- A collapsed `1..1` or `3..3` range means cancellation corrupted selection.
- An `input` entry means a canceled default action still emitted mutation.
- A `change` entry means blur committed a dirty state that never existed.
- A focus byte other than 4 means the next key did not reuse retained state.
- A nonempty target after blur means selection lifetime leaked past focus.

## Scope

This scenario covers cancellation state, UTF-8 byte offsets, event ordering,
host/worker parity, subsequent keyboard selection, and blur cleanup. It does
not add composition-event semantics, clipboard behavior, or a second selection
model; those require separate executable requirements.

## Frozen Steps

The displayed scenario keeps these manual steps in order:

1. Cancel hosted Backspace and Delete over the UTF-8 selection.
2. Extend the retained hosted selection and clear it on blur.
3. Cancel worker K2 Backspace and Delete over the same selection.
4. Extend the retained worker selection and clear it on blur.

The helper checks are executable assertions, not additional event paths or
state owners.

## Scenarios

### Canceled browser text editing

#### should preserve selection and event ordering across hosted and worker paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-007
# @req REQ-WEB-BROWSER-008
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/04_architecture/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-007`
- `REQ-WEB-BROWSER-008`
- `REQ-WEB-BROWSER-007:`
- `REQ-WEB-BROWSER-008:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c262975df6e08de83f40c7dac7d5fe2a555cdfc93f6e97ba1844b02ab9c3e44e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c262975df6e08de83f40c7dac7d5fe2a555cdfc93f6e97ba1844b02ab9c3e44e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c262975df6e08de83f40c7dac7d5fe2a555cdfc93f6e97ba1844b02ab9c3e44e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_text_edit_cancellation_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/app/browser/feature/browser_text_edit_cancellation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_text_edit_cancellation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl:169:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should preserve selection and event ordering across hosted and worker paths' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/browser/feature/browser_text_edit_cancellation_spec.spl:169:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve selection and event ordering across hosted and worker paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
