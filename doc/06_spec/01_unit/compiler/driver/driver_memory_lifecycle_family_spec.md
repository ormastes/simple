# Contract spec: test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl` |
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
`bin/simple test test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl` and a green Results line.

## Scenarios

### driver memory lifecycle family invariants

#### keeps the three phase evictions reference-drop only

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the three phase evictions reference-drop only


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the three phase evictions reference-drop only")
val source = file_read(TYPES)
expect(source).to_contain("me evict_ast():")
expect(source).to_contain("me evict_hir():")
# No deep-free CALL anywhere in the driver context (the name appears once
# more, in the prohibition comment asserted by the next example).
expect(source).to_not_contain("rt_dict_free_deep(")
```

</details>

#### retains the measured rationale that forbids a deep free

- retains the measured rationale that forbids a deep free


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("retains the measured rationale that forbids a deep free")
val source = file_read(TYPES)
expect(source).to_contain("Do NOT \"fix\" this by calling rt_dict_free_deep here")
expect(source).to_contain("reclaims NOTHING")
```

</details>

#### records that the real fix is a codegen change, not a driver change

- records that the real fix is a codegen change, not a driver change


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records that the real fix is a codegen change, not a driver change")
val source = file_read(TYPES)
expect(source).to_contain("NOT a driver change")
```

</details>

<details>
<summary>Advanced: never constructs the HIR lowerer inside the per-source loop</summary>

#### never constructs the HIR lowerer inside the per-source loop

- never constructs the HIR lowerer inside the per-source loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never constructs the HIR lowerer inside the per-source loop")
val source = file_read(HIR)
val loop = source.index_of("while source_idx < self.ctx.sources.len():")
expect(loop).to_be_greater_than(0)
val body = source.substring(loop, source.len())
expect(body).to_not_contain("hirlowering_for_module_with_diagnostics(")        expect(body).to_not_contain("hirlowering_new()")
```

</details>


</details>

#### reuses one diagnostics buffer and one trait-registry owner

- reuses one diagnostics buffer and one trait-registry owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reuses one diagnostics buffer and one trait-registry owner")
val source = file_read(HIR)
expect(source).to_contain("Allocate the diagnostics array before the long HIR loop")
expect(source).to_contain("This loop-owned lowerer is the trait registry owner")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `ca175fa31f78c233bc1ffceb2f8a80a4f1e822dfb23f8ad61b47bf5f3f063111`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca175fa31f78c233bc1ffceb2f8a80a4f1e822dfb23f8ad61b47bf5f3f063111`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca175fa31f78c233bc1ffceb2f8a80a4f1e822dfb23f8ad61b47bf5f3f063111`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the three phase evictions reference-drop only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the measured rationale that forbids a deep free' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records that the real fix is a codegen change, not a driver change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
