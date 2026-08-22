# minimal_bootstrap_configuration_composed_dynamic_architecture_spec

> Verifies the minimal bootstrap configuration composed dynamic architecture behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# minimal_bootstrap_configuration_composed_dynamic_architecture_spec

Verifies the minimal bootstrap configuration composed dynamic architecture behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the minimal bootstrap configuration composed dynamic architecture behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Minimal-bootstrap composition development

#### compiles canonical application configuration into validated SCI v1

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Compile and inspect one immutable composition image (expected show, folded, detail, or skip)


- Verify: compiles canonical application configuration into validated SCI v1
- compile_composition
- check_composition_image
   - Expected: check_composition_image(image, "Notes") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-008 REQ-011 REQ-012 REQ-014 REQ-015 REQ-003
step("Verify: compiles canonical application configuration into validated SCI v1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""An application-catalog edit is compiled as configuration data. The
reader validates the resulting image before any launcher state changes."""
step("compile_composition")
val image = compile_composition(setup_minimal_bootstrap_fixture("Notes"))
step("check_composition_image")
expect(check_composition_image(image, "Notes")).to_equal(true)
```

</details>

#### round-trips interface provider binding and command metadata in SCI

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Compile CLI command and provider selection as data (expected show, folded, detail, or skip)


- Verify: round-trips interface provider binding and command metadata in SCI
- compile_composition
   - Expected: check_cli_composition_section() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-005 REQ-007 REQ-011 REQ-012 REQ-014 REQ-015 REQ-003
step("Verify: round-trips interface provider binding and command metadata in SCI")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Command names, aliases, summaries, locked artifacts, interface
versions, and binding selection are configuration records rather than
imports in this executable codec proof."""
step("compile_composition")
expect(check_cli_composition_section()).to_equal(true)
```

</details>

#### loads renamed application metadata in one unchanged launcher process

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Reload catalog data without replacing launcher code (expected show, folded, detail, or skip)


- Verify: loads renamed application metadata in one unchanged launcher process
- load_unchanged_core
   - Expected: load_unchanged_core(first, second) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-005 REQ-007 REQ-011 REQ-012 REQ-014 REQ-015
step("Verify: loads renamed application metadata in one unchanged launcher process")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""The proof currently holds the launcher process constant while two
independently validated SCI projections are loaded. Binary-hash
containment remains a later build-target acceptance row."""
val first = compile_composition(setup_minimal_bootstrap_fixture("Notes"))
val second = compile_composition(setup_minimal_bootstrap_fixture("Knowledge Notes"))
step("load_unchanged_core")
expect(load_unchanged_core(first, second)).to_equal(true)
```

</details>

#### projects shortcuts and fails closed on capability or association owner gaps

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Project supported launcher policy and reject unsupported authority (expected show, folded, detail, or skip)


- Verify: projects shortcuts and fails closed on capability or association owner gaps
- check_launcher_policy_projection
   - Expected: check_launcher_policy_projection() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-008 REQ-011 REQ-012 REQ-003
step("Verify: projects shortcuts and fails closed on capability or association owner gaps")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Shortcut key/modifier data uses the existing launcher registration
owner. Scoped capabilities and associations reject before mutation;
their exact owner-API gaps are tracked in the linked bug record."""
step("check_launcher_policy_projection")
expect(check_launcher_policy_projection()).to_equal(true)
```

</details>

#### dispatches an admitted in-process provider and keeps dynamic modes fail closed

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Query and dispatch one leaf command provider (expected show, folded, detail, or skip)


- Verify: dispatches an admitted in-process provider and keeps dynamic modes fail closed
- dispatch_provider
   - Expected: receipt.status equals `SIMPLE_CLI_OK`
   - Expected: text.from_bytes(receipt.output) equals `formatted:notes.spl`
   - Expected: simple_provider_query_dynamic_v1(SIMPLE_PROVIDER_MODE_NATIVE).status equals `SIMPLE_PROVIDER_NOT_PROCESS_CALLABLE`
   - Expected: simple_provider_query_dynamic_v1(SIMPLE_PROVIDER_MODE_SMF).status equals `SIMPLE_PROVIDER_NOT_PROCESS_CALLABLE`
   - Expected: check_provider_generation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-005 REQ-007 REQ-008 REQ-014 REQ-015 REQ-003
step("Verify: dispatches an admitted in-process provider and keeps dynamic modes fail closed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""The numeric provider descriptors are ABI-safe. This scenario proves
executable in-process query and command dispatch; native and SMF modes
remain rejected until their loaders prove a process-callable entry."""
step("dispatch_provider")
val receipt = dispatch_provider()
expect(receipt.status).to_equal(SIMPLE_CLI_OK)
expect(text.from_bytes(receipt.output)).to_equal("formatted:notes.spl")
expect(simple_provider_query_dynamic_v1(SIMPLE_PROVIDER_MODE_NATIVE).status).to_equal(SIMPLE_PROVIDER_NOT_PROCESS_CALLABLE)
expect(simple_provider_query_dynamic_v1(SIMPLE_PROVIDER_MODE_SMF).status).to_equal(SIMPLE_PROVIDER_NOT_PROCESS_CALLABLE)
expect(check_provider_generation()).to_equal(true)
```

</details>

#### never treats unknown compatibility as reusable

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Explain conservative rebuild decisions (expected show, folded, detail, or skip)


- Verify: never treats unknown compatibility as reusable
- explain_rebuild
   - Expected: compatibility_allows_reuse(receipt.compatibility) is false
- check_rebuild_receipt
   - Expected: check_rebuild_receipt(receipt) is true
- check_bootstrap_reason
   - Expected: check_bootstrap_reason(receipt) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-005 REQ-007 REQ-008 REQ-011 REQ-012 REQ-014 REQ-015 REQ-003
step("Verify: never treats unknown compatibility as reusable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Unknown compatibility selects the smallest declared producer
rebuild and never becomes cache-reuse evidence."""
step("explain_rebuild")
val receipt = explain_rebuild()
expect(compatibility_allows_reuse(receipt.compatibility)).to_equal(false)
step("check_rebuild_receipt")
expect(check_rebuild_receipt(receipt)).to_equal(true)
step("check_bootstrap_reason")
expect(check_bootstrap_reason(receipt)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `124a600855467bd84113c689de00dcca0a901db5f09e4632732c32c5c2f370fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `124a600855467bd84113c689de00dcca0a901db5f09e4632732c32c5c2f370fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `124a600855467bd84113c689de00dcca0a901db5f09e4632732c32c5c2f370fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.spl
mirror: doc/06_spec/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple/feature/minimal_bootstrap_configuration_composed_dynamic_architecture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
