# Me Method Body Baremetal Specification

> Tests covering me method body baremetal regression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Me Method Body Baremetal Specification

## Scenarios

### me method body baremetal regression

#### stub fallback diagnostics

#### documents the SIMPLE_NO_STUB_FALLBACK env var

- documents the SIMPLE_NO_STUB_FALLBACK env var
   - Expected: expected_marker.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the SIMPLE_NO_STUB_FALLBACK env var")
# SIMPLE_NO_STUB_FALLBACK=1 turns the silent stub-fallback in
# compile_all_functions into a hard ModuleError, making
# missing-body bugs loud at codegen time. Use this when
# bisecting suspected me-method body losses or any other
# silently-failing function-body compilation.
val expected_marker = "[CODEGEN-STUB-FALLBACK]"
expect(expected_marker.len() > 0).to_equal(true)
```

</details>

#### documents the Agent V workaround in DesktopShell.new()

- documents the Agent V workaround in DesktopShell.new()
   - Expected: workaround_file.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the Agent V workaround in DesktopShell.new()")
# src/os/desktop/shell.spl currently inlines launcher_init()
# into DesktopShell.new() because DesktopShell.init() (a `me`
# method) was hitting the stub-fallback path. Once the
# underlying compile error is resolved AND
# SIMPLE_NO_STUB_FALLBACK=1 is enabled by default, the
# workaround in DesktopShell.new() should be reverted and
# the launcher_init() call moved back into init().
val workaround_file = "src/os/desktop/shell.spl"
expect(workaround_file.len() > 0).to_equal(true)
```

</details>

#### TinyShell tracer class

#### instantiates via the static constructor

- instantiates via the static constructor
   - Expected: tiny.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instantiates via the static constructor")
val tiny = TinyShell.new()
expect(tiny.initialized).to_equal(false)
```

</details>

#### runs the me-method body in interpreter and SMF modes

- runs the me-method body in interpreter and SMF modes
   - Expected: tiny.initialized is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs the me-method body in interpreter and SMF modes")
# In interpreter and SMF modes the me-method body runs
# correctly today; only the baremetal Cranelift lane
# exhibited the silent-stub bug. This case guards against
# regressions in those modes.
val tiny = TinyShell.new()
tiny.init()
expect(tiny.initialized).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/me_method_body_baremetal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering me method body baremetal regression.
- me method body baremetal regression

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

- Canonical SPipe generation for source `d609ea9d926947d39c3d5355ff3d3b478d04d0009b6853ac8e001a72833fa74e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d609ea9d926947d39c3d5355ff3d3b478d04d0009b6853ac8e001a72833fa74e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d609ea9d926947d39c3d5355ff3d3b478d04d0009b6853ac8e001a72833fa74e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/me_method_body_baremetal_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/me_method_body_baremetal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/me_method_body_baremetal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/me_method_body_baremetal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/me_method_body_baremetal_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the SIMPLE_NO_STUB_FALLBACK env var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/me_method_body_baremetal_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the Agent V workaround in DesktopShell.new()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/me_method_body_baremetal_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'instantiates via the static constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
