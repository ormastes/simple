# Cached Render Entry Closure Contract

> This specification checks the durable recovery contract without claiming that

Focused behavioral companion:
`cached_render_entry_closure_runtime_selection_spec.md`. It covers configured
candidate priority, canonical Rust-seed rejection, and missing-candidate
nonzero preflight without claiming Stage 4 admission.

This operator manual mirrors
`test/03_system/check/cached_render_entry_closure_contract_spec.spl`. It is
checked in so the blocked lane remains discoverable; TODO688 requires canonical
`spipe-docgen` regeneration before this manual is admitted as generated evidence.

<details>
<summary>Full Scenario Manual</summary>

# Cached Render Entry Closure Contract

This specification checks the durable recovery contract without claiming that

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/cached_render_entry_closure_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This specification checks the durable recovery contract without claiming that
the blocked Stage 4 CLI or 8K carrier has executed. It binds operator discovery,
fail-closed pure-Simple ownership, and the exact sparse evidence boundary.

## Scenarios

### CachedRenderEntryClosureV1 system contract

#### should expose the canonical interface from the operator guide

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Operator discovery and honest status (expected show, folded, detail, or skip)


- should expose the canonical interface from the operator guide
- Open the cached render entry-closure guide


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the canonical interface from the operator guide")
step("Open the cached render entry-closure guide")
val guide = file_read(GUIDE)
expect(guide).to_contain("CachedRenderEntryClosureV1")
expect(guide).to_contain("currently **blocked**")
```

</details>

#### should link the plan and blocker from the guide

- should link the plan and blocker from the guide
- Inspect operator recovery links


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should link the plan and blocker from the guide")
step("Inspect operator recovery links")
val guide = file_read(GUIDE)
expect(guide).to_contain(PLAN)
expect(guide).to_contain(BUG)
```

</details>

#### should reject unavailable production wording

- should reject unavailable production wording
- Check that the guide labels the workflow as planned evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject unavailable production wording")
step("Check that the guide labels the workflow as planned evidence")
val guide = file_read(GUIDE)
expect(guide).to_contain("planned production-evidence workflow")
```

</details>

#### should name the pure-Simple native-build owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Fail-closed CLI ownership (expected show, folded, detail, or skip)


- should name the pure-Simple native-build owners
- Inspect the tracked blocker ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should name the pure-Simple native-build owners")
step("Inspect the tracked blocker ownership")
val bug = file_read(BUG)
expect(bug).to_contain("src/app/cli/_CliMain/main_and_help.spl")
expect(bug).to_contain("src/app/io/_CliCompile/compile_targets.spl")
expect(bug).to_contain("src/app/cli/native_build_main.spl")
```

</details>

#### should treat success without an artifact as failure

- should treat success without an artifact as failure
- Inspect the missing-artifact acceptance rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should treat success without an artifact as failure")
step("Inspect the missing-artifact acceptance rule")
val bug = file_read(BUG)
expect(bug).to_contain("exit 0")
expect(bug).to_contain("no output artifact")
```

</details>

#### should forbid seed and stale-artifact substitution

- should forbid seed and stale-artifact substitution
- Inspect the plan fail-closed policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should forbid seed and stale-artifact substitution")
step("Inspect the plan fail-closed policy")
val plan = file_read(PLAN)
expect(plan).to_contain("seed")
expect(plan).to_contain("stale artifact")
expect(plan).to_contain("fails closed")
```

</details>

#### should preserve the canonical sparse corpus dimensions

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Sparse executor evidence boundary (expected show, folded, detail, or skip)


- should preserve the canonical sparse corpus dimensions
- Inspect viewport frame and damage requirements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the canonical sparse corpus dimensions")
step("Inspect viewport frame and damage requirements")
val plan = file_read(PLAN)
expect(plan).to_contain("7680x4320")
expect(plan).to_contain("20 frames")
expect(plan).to_contain("256x128")
```

</details>

#### should require correctness and traversal receipts

- should require correctness and traversal receipts
- Inspect sparse correctness requirements


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require correctness and traversal receipts")
step("Inspect sparse correctness requirements")
val plan = file_read(PLAN)
expect(plan).to_contain("two considered and 512 culled")
expect(plan).to_contain("nonzero readback")
expect(plan).to_contain("zero full-frame mismatches")
expect(plan).to_contain("stable checksum")
```

</details>

#### should retain performance identity and claim boundaries

- should retain performance identity and claim boundaries
- Inspect budget identity and exclusion requirements


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain performance identity and claim boundaries")
step("Inspect budget identity and exclusion requirements")
val plan = file_read(PLAN)
expect(plan).to_contain("p50 and p95 each at most 12.5 ms")
expect(plan).to_contain("binary/source hashes")
expect(plan).to_contain("sparse executor")
expect(plan).to_contain("not presentation")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fdbbc45fc385705d888287421a80f5f775f17c362f6cacb3bd8758d02e0ebde3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdbbc45fc385705d888287421a80f5f775f17c362f6cacb3bd8758d02e0ebde3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdbbc45fc385705d888287421a80f5f775f17c362f6cacb3bd8758d02e0ebde3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/check/cached_render_entry_closure_contract_spec.spl
mirror: doc/06_spec/03_system/check/cached_render_entry_closure_contract_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/cached_render_entry_closure_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/cached_render_entry_closure_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the canonical interface from the operator guide' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the canonical interface from the operator guide' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should link the plan and blocker from the guide' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should link the plan and blocker from the guide' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unavailable production wording' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject unavailable production wording' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should name the pure-Simple native-build owners' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should treat success without an artifact as failure' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/check/cached_render_entry_closure_contract_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should forbid seed and stale-artifact substitution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
