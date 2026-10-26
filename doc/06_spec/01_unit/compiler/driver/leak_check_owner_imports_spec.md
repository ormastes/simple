# Contract spec: test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl` |
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
`bin/simple test test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl` and a green Results line.

## Scenarios

### leak check owner imports

#### tracker operations from concrete owners run end to end

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- imports the interpreter call and result type from concrete owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("imports the interpreter call and result type from concrete owners")
val source = rt_file_read_text("src/compiler/tools/leak_check/main.spl") ?? ""
expect(source).to_contain("use compiler.driver.driver_public_interpret_bridge.\{interpret_file\}")
expect(source).to_contain("use compiler.common.driver_core_types.\{CompileResult\}")
expect(source).to_not_contain("use compiler.driver.\{interpret_file, CompileResult\}")
```

</details>

#### MemLeakEntry from its concrete owner carries the pinned fields

- imports MemLeakEntry directly while retaining adjacent tracker operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("imports MemLeakEntry directly while retaining adjacent tracker operations")
val source = rt_file_read_text("src/compiler/tools/leak_check/main.spl") ?? ""
expect(source).to_contain("use std.mem_tracker.types.\{MemLeakEntry\}")
expect(source).to_contain("mem_enable, mem_disable, mem_snapshot, mem_dump_leaks, parse_leak_dump")
expect(source).to_not_contain("parse_leak_dump, MemLeakEntry")
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed99f9476a89af7f2f29e430207b28a792d5aae19741e0ad89d20662bf5077c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed99f9476a89af7f2f29e430207b28a792d5aae19741e0ad89d20662bf5077c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed99f9476a89af7f2f29e430207b28a792d5aae19741e0ad89d20662bf5077c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/leak_check_owner_imports_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports the interpreter call and result type from concrete owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports MemLeakEntry directly while retaining adjacent tracker operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
