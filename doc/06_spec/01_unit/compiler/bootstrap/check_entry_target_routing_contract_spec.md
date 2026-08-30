# Contract spec: test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl` and a green Results line.

## Scenarios

### check entry target routing

#### does not classify the reserved-looking target basename as argv metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not classify the reserved-looking target basename as argv metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not classify the reserved-looking target basename as argv metadata")
val source = file_read("src/app/cli/check_entry.spl")
expect(source).to_contain("if i == 0 and arg == \"check\":")
# Was `to_contain("a source")`, which matched only the rationale
# comment. Anchored instead to the real consume-then-continue body:
# nothing but an exact leading "check" token may be dropped.
expect(source).to_contain("if i == 0 and arg == \"check\":\n            i = i + 1\n            continue\n        out.push(arg)")
expect(source).to_not_contain("arg.ends_with(\"check_entry.spl\")")
```

</details>

#### still consumes the explicit adjacent check command discriminator

- still consumes the explicit adjacent check command discriminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still consumes the explicit adjacent check command discriminator")
val source = file_read("src/app/cli/check_entry.spl")
expect(source).to_contain("i == 0 and arg == \"check\"")
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ce6701120169109b1ebb379825c44a498ecc0824aafd6a1c36258350d4b88046`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce6701120169109b1ebb379825c44a498ecc0824aafd6a1c36258350d4b88046`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce6701120169109b1ebb379825c44a498ecc0824aafd6a1c36258350d4b88046`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not classify the reserved-looking target basename as argv metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still consumes the explicit adjacent check command discriminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
