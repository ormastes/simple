# T32 Backend: Python RCL Bridge

> Tests core T32 operations using the Python RCL bridge backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Backend: Python RCL Bridge

Tests core T32 operations using the Python RCL bridge backend.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/backends/python_rcl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests core T32 operations using the Python RCL bridge backend.
Requires python3 and lauterbach.trace32.rcl package.

## Scenarios

### T32 via Python RCL backend

#### when Python RCL is available

#### python binary exists

- python binary exists
   - Expected: t32_hw_python_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("python binary exists")
if not t32_hw_python_available():
    expect("python not available").to_contain("not available")
    return
if not t32_hw_has_software_build():
    expect("SOFTWARE.BUILD not available in this T32 version -- Python RCL requires newer T32").to_contain("not available")
    return
expect(t32_hw_python_available()).to_equal(true)
```

</details>

#### connects and pings

- connects and pings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connects and pings")
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_connect_and_ping()
```

</details>

#### evaluates VERSION.BUILD()

- evaluates VERSION.BUILD()


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("evaluates VERSION.BUILD()")
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_eval_version()
```

</details>

#### runs PRACTICE command

- runs PRACTICE command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs PRACTICE command")
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_cmd_run()
```

</details>

#### queries STATE.RUN()

- queries STATE.RUN()


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("queries STATE.RUN()")
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_state_query()
```

</details>

#### reads PC register

- reads PC register


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads PC register")
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_register_read()
```

</details>

#### halt-step-halt cycle

- halt-step-halt cycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("halt-step-halt cycle")
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_step_and_halt()
```

</details>

#### recovers from error

- recovers from error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("recovers from error")
if not t32_hw_python_available() or not t32_hw_has_software_build():
    expect("Python RCL skipped: requires python + newer T32 with SOFTWARE.BUILD").to_contain("skipped")
    return
shared_test_error_recovery()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca5079c30af25df224b1de3d02aae8c4aa53c36d0cb8ab2e3f93ba32e1e0534e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca5079c30af25df224b1de3d02aae8c4aa53c36d0cb8ab2e3f93ba32e1e0534e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca5079c30af25df224b1de3d02aae8c4aa53c36d0cb8ab2e3f93ba32e1e0534e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/backends/python_rcl_spec.spl
mirror: doc/06_spec/integration/t32_hw/backends/python_rcl_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/backends/python_rcl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/backends/python_rcl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/backends/python_rcl_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'python binary exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/backends/python_rcl_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects and pings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/backends/python_rcl_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates VERSION.BUILD()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
