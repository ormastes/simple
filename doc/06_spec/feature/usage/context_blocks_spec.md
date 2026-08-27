# context_blocks_spec

> Purpose: the scoped-resource contract (setup frames the body, teardown

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# context_blocks_spec

Purpose: the scoped-resource contract (setup frames the body, teardown

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/feature/usage/context_blocks_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: the scoped-resource contract (setup frames the body, teardown
closes it, nesting unwinds innermost-first, scope-local bindings never leak)
is observed as pure value transforms — the framing `scoped*` helpers are the
semantic core a `context` block desugars onto. Audience: language engineers
designing the `context` block surface.

## Scenarios

### Context Blocks

#### Basic context execution

#### frames the body's events with the scope's setup and teardown

- Verify: body events run inside the scoped frame
   - Expected: log equals `["setup", "body", "teardown"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: body events run inside the scoped frame")
val log = scoped(["body"])
expect(log).to_equal(["setup", "body", "teardown"])  # oracle: full scoped frame
```

</details>

#### Setup and teardown

#### an empty body still yields both frame events in order

- Verify: ordering is setup, teardown even with no body work
   - Expected: log equals `["setup", "teardown"]`
   - Expected: log.first() equals `setup`
   - Expected: log.last() equals `teardown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: ordering is setup, teardown even with no body work")
val log = scoped([])
expect(log).to_equal(["setup", "teardown"])  # oracle: frame is unconditional
expect(log.first()).to_equal("setup")  # oracle: setup precedes everything
expect(log.last()).to_equal("teardown")  # oracle: teardown follows everything
```

</details>

#### Nested contexts

#### unwinds nested scopes innermost-first

- Verify: inner exit precedes outer exit in the event trace
   - Expected: log equals `["outer:enter", "inner:enter", "body", "inner:exit", "outer:exit"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: inner exit precedes outer exit in the event trace")
val log = scoped_named("outer", scoped_named("inner", ["body"]))
expect(log).to_equal(["outer:enter", "inner:enter", "body", "inner:exit", "outer:exit"])  # oracle: LIFO unwinding
```

</details>

#### Context variables

#### a binding inside the scope appears only inside the frame

- Verify: scope-local binding produces its value inside, nothing outside
   - Expected: log equals `["setup", "inside", "teardown"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Verify: scope-local binding produces its value inside, nothing outside")
val scoped_name = "inside"
val log = scoped([scoped_name])
expect(log).to_equal(["setup", "inside", "teardown"])  # oracle: inner value appears exactly once, within the frame
```

</details>

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0e63b355196e566b4c380349cfb19ef76de39e54c521ba2474ca73c4d97cdd30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e63b355196e566b4c380349cfb19ef76de39e54c521ba2474ca73c4d97cdd30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e63b355196e566b4c380349cfb19ef76de39e54c521ba2474ca73c4d97cdd30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/context_blocks_spec.spl
mirror: doc/06_spec/feature/usage/context_blocks_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/context_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/context_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/context_blocks_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'frames the body's events with the scope's setup and teardown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/context_blocks_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an empty body still yields both frame events in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/context_blocks_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwinds nested scopes innermost-first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
