# Command Resolver Specification

> Tests covering minimal simple-core command resolver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Command Resolver Specification

## Scenarios

### minimal simple-core command resolver

#### exposes only the fixed CLI-0 command surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes only the fixed CLI-0 command surface
   - Expected: default_help.status equals `SIMPLE_CORE_OK`
   - Expected: help.status equals `SIMPLE_CORE_OK`
   - Expected: help.output does not contain `compile`
   - Expected: help.output does not contain `office`
   - Expected: version.status equals `SIMPLE_CORE_OK`
   - Expected: version.output equals `simple-core 1.2.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes only the fixed CLI-0 command surface")
val default_help = simple_core_resolve_v1([], valid_core_config(), "1.2.3")
expect(default_help.status).to_equal(SIMPLE_CORE_OK)

val help = simple_core_resolve_v1(["--help"], valid_core_config(), "1.2.3")
expect(help.status).to_equal(SIMPLE_CORE_OK)
expect(help.output).to_contain("config verify")
expect(help.output).to_contain("provider inspect")
expect(help.output).to_contain("doctor")
expect(help.output.contains("compile")).to_equal(false)
expect(help.output.contains("office")).to_equal(false)

val version = simple_core_resolve_v1(["--version"], valid_core_config(), "1.2.3")
expect(version.status).to_equal(SIMPLE_CORE_OK)
expect(version.output).to_equal("simple-core 1.2.3")
```

</details>

#### verifies the decoded SCI result without reparsing source configuration

- verifies the decoded SCI result without reparsing source configuration
   - Expected: accepted.status equals `SIMPLE_CORE_OK`
   - Expected: result.status equals `SIMPLE_CORE_CONFIG_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies the decoded SCI result without reparsing source configuration")
val accepted = simple_core_resolve_v1(["config", "verify"], valid_core_config(), "1.2.3")
expect(accepted.status).to_equal(SIMPLE_CORE_OK)
expect(accepted.output).to_contain("SCI_OK")

val rejected = CompositionReadResultV1(
    ok: false,
    image: empty_composition_image_v1(),
    diagnostic: composition_diagnostic_v1("SCI_COMPOSITION_DIGEST", "header", "digest mismatch"),
)
val result = simple_core_resolve_v1(["config", "verify"], rejected, "1.2.3")
expect(result.status).to_equal(SIMPLE_CORE_CONFIG_INVALID)
expect(result.diagnostic).to_contain("SCI_COMPOSITION_DIGEST")

val extra = simple_core_resolve_v1(["config", "verify", "unexpected"], valid_core_config(), "1.2.3")
expect(extra.diagnostic).to_contain("accepts no additional arguments")
```

</details>

#### inspects immutable provider declarations without activating code

- inspects immutable provider declarations without activating code
   - Expected: found.status equals `SIMPLE_CORE_OK`
   - Expected: missing.status equals `SIMPLE_CORE_PROVIDER_NOT_FOUND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inspects immutable provider declarations without activating code")
val found = simple_core_resolve_v1(["provider", "inspect", "formatter"], valid_core_config(), "1.2.3")
expect(found.status).to_equal(SIMPLE_CORE_OK)
expect(found.output).to_contain("build/providers/fmt.smf")
expect(found.output).to_contain("cli.command")

val missing = simple_core_resolve_v1(["provider", "inspect", "missing"], valid_core_config(), "1.2.3")
expect(missing.status).to_equal(SIMPLE_CORE_PROVIDER_NOT_FOUND)

val absent_id = simple_core_resolve_v1(["provider", "inspect"], valid_core_config(), "1.2.3")
expect(absent_id.diagnostic).to_contain("exactly one provider id")
```

</details>

#### fails closed for invalid config and commands outside CLI-0

- fails closed for invalid config and commands outside CLI-0
   - Expected: doctor.status equals `SIMPLE_CORE_CONFIG_INVALID`
   - Expected: healthy.status equals `SIMPLE_CORE_OK`
   - Expected: provider_rejected.status equals `SIMPLE_CORE_CONFIG_INVALID`
   - Expected: extended.status equals `SIMPLE_CORE_INVALID_COMMAND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for invalid config and commands outside CLI-0")
val rejected = CompositionReadResultV1(
    ok: false,
    image: empty_composition_image_v1(),
    diagnostic: composition_diagnostic_v1("SCI_TRUNCATED", "header", "truncated"),
)
val doctor = simple_core_resolve_v1(["doctor"], rejected, "1.2.3")
expect(doctor.status).to_equal(SIMPLE_CORE_CONFIG_INVALID)
expect(doctor.diagnostic).to_contain("SCI_TRUNCATED")

val healthy = simple_core_resolve_v1(["doctor"], valid_core_config(), "1.2.3")
expect(healthy.status).to_equal(SIMPLE_CORE_OK)
expect(healthy.output).to_contain("providers=1")

val provider_rejected = simple_core_resolve_v1(["provider", "inspect", "formatter"], rejected, "1.2.3")
expect(provider_rejected.status).to_equal(SIMPLE_CORE_CONFIG_INVALID)

val extended = simple_core_resolve_v1(["compile"], valid_core_config(), "1.2.3")
expect(extended.status).to_equal(SIMPLE_CORE_INVALID_COMMAND)
expect(extended.diagnostic).to_contain("not a static simple-core command")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_core/command_resolver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering minimal simple-core command resolver.
- minimal simple-core command resolver

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

- Canonical SPipe generation for source `76f89e1aba2291be5ee0b0e9a36e4f12de74cacc180aa1b11f0990b421431c83`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76f89e1aba2291be5ee0b0e9a36e4f12de74cacc180aa1b11f0990b421431c83`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76f89e1aba2291be5ee0b0e9a36e4f12de74cacc180aa1b11f0990b421431c83`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/simple_core/command_resolver_spec.spl
mirror: doc/06_spec/01_unit/app/simple_core/command_resolver_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/simple_core/command_resolver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_core/command_resolver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_core/command_resolver_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes only the fixed CLI-0 command surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_core/command_resolver_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies the decoded SCI result without reparsing source configuration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_core/command_resolver_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inspects immutable provider declarations without activating code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
