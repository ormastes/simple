# Debug Config Literal Fields Specification

> Tests covering DebugConfig literals only name declared fields.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Config Literal Fields Specification

## Scenarios

### DebugConfig literals only name declared fields

#### no DebugConfig declaration in the tree carries args/debugger/remote

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- no DebugConfig declaration in the tree carries args/debugger/remote


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no DebugConfig declaration in the tree carries args/debugger/remote")
val decls = [
    src_of("src/app/debug/remote/types.spl"),
    src_of("src/lib/nogc_sync_mut/debug/remote/types.spl"),
    src_of("src/lib/nogc_async_mut/debug/remote/types.spl"),
    src_of("src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl")
]
for decl in decls:
    assert_true(decl.len() > 0)
    expect(decl).to_contain("class DebugConfig")
    expect(decl).to_contain("    host: text")
    expect(decl).to_contain("    program: text")
    assert_false(decl.contains("\n    args:"))
    assert_false(decl.contains("\n    debugger:"))
    assert_false(decl.contains("\n    remote:"))
```

</details>

#### the trace32 construction sites no longer pass undeclared fields

- the trace32 construction sites no longer pass undeclared fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the trace32 construction sites no longer pass undeclared fields")
val power = src_of("src/lib/nogc_sync_mut/terminal/power/t32_power.spl")
val hw = src_of("src/app/test_daemon/adapters/hardware_adapter.spl")
assert_true(power.len() > 0)
assert_true(hw.len() > 0)
assert_false(power.contains("debugger: \"t32\""))
assert_false(power.contains("remote: true"))
assert_false(hw.contains("debugger: \"t32\""))
assert_false(hw.contains("remote: true"))
```

</details>

#### the trace32 sites use the declared-field constructor helper

- the trace32 sites use the declared-field constructor helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the trace32 sites use the declared-field constructor helper")
expect(src_of("src/lib/nogc_sync_mut/terminal/power/t32_power.spl")).to_contain("DebugConfig.for_trace32(")
expect(src_of("src/app/test_daemon/adapters/hardware_adapter.spl")).to_contain("DebugConfig.for_trace32(")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/debug_config_literal_fields_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DebugConfig literals only name declared fields.
- DebugConfig literals only name declared fields

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

- `REQ-SSPEC-UNIT`
- `REQ-JIT-FIELD-INFER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e563983a1c5ada272d56896797aeb2d4a14da74e1bde8babfb68f267f9bf074e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e563983a1c5ada272d56896797aeb2d4a14da74e1bde8babfb68f267f9bf074e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e563983a1c5ada272d56896797aeb2d4a14da74e1bde8babfb68f267f9bf074e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/debug_config_literal_fields_spec.spl
mirror: doc/06_spec/unit/lib/debug_config_literal_fields_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/unit/lib/debug_config_literal_fields_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/debug_config_literal_fields_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/debug_config_literal_fields_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/debug_config_literal_fields_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no DebugConfig declaration in the tree carries args/debugger/remote' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/debug_config_literal_fields_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the trace32 construction sites no longer pass undeclared fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/debug_config_literal_fields_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the trace32 sites use the declared-field constructor helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
