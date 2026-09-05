# Driver Main Cli Contract Specification

> Tests covering pure-Simple driver CLI contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Main Cli Contract Specification

## Scenarios

### pure-Simple driver CLI contract

#### accepts --target in both spaced and = forms

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts --target in both spaced and = forms


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts --target in both spaced and = forms")
val source = file_read(MAIN)
expect(source).to_contain("elif arg == \"--target\":")
expect(source).to_contain("elif arg.starts_with(\"--target=\"):")
# The value must reach the parsed args, not just be swallowed.
expect(source).to_contain("cli_args.target = ")
```

</details>

#### maps the target onto a codegen backend rather than dropping it

- maps the target onto a codegen backend rather than dropping it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps the target onto a codegen backend rather than dropping it")
val source = file_read(MAIN)
val idx = source.index_of("Map `--target` to the codegen backend")
expect(idx).to_be_greater_than(0)
```

</details>

#### declares --target before the unknown-option catch-all

- declares --target before the unknown-option catch-all


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares --target before the unknown-option catch-all")
# `elif arg.starts_with("-")` rejects anything it reaches first, which is
# exactly how --target used to fail. Order is the contract.
val source = file_read(MAIN)
val target_arm = source.index_of("elif arg == \"--target\":")
expect(target_arm).to_be_greater_than(0)
# There is an earlier, unrelated `starts_with("-")` arm in the bootstrap
# pre-scan loop, so anchor the search at the --target arm itself.
val catch_all = source.index_of("elif arg.starts_with(\"-\"):", target_arm)
expect(catch_all).to_be_greater_than(target_arm)
```

</details>

#### routes --check through a real compile mode, not a no-op

- routes --check through a real compile mode, not a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes --check through a real compile mode, not a no-op")
val source = file_read(MAIN)
expect(source).to_contain("elif arg == \"-k\" or arg == \"--check\":")
expect(source).to_contain("requested_mode_text = \"check\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/driver_main_cli_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple driver CLI contract.
- pure-Simple driver CLI contract

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

- Canonical SPipe generation for source `165d1ae6b5d00f2d01b920dec92908aa8b09f0b6e4344f43471deadb845cbea2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `165d1ae6b5d00f2d01b920dec92908aa8b09f0b6e4344f43471deadb845cbea2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `165d1ae6b5d00f2d01b920dec92908aa8b09f0b6e4344f43471deadb845cbea2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/driver_main_cli_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/driver_main_cli_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/driver_main_cli_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/driver_main_cli_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/driver_main_cli_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts --target in both spaced and = forms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_main_cli_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps the target onto a codegen backend rather than dropping it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_main_cli_contract_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares --target before the unknown-option catch-all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
