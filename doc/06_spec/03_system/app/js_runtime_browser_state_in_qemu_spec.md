# js_runtime_browser_state_in_qemu_spec

> Verifies the js runtime browser state in qemu behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# js_runtime_browser_state_in_qemu_spec

Verifies the js runtime browser state in qemu behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the js runtime browser state in qemu behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### JS runtime browser-state probe in QEMU Simple OS guest

#### builds the Cranelift kernel

- Verify: builds the Cranelift kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_JS_RUNTIME_BROWSER_STATE-001
step("Verify: builds the Cranelift kernel")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_runtime_probe_build("cranelift")
```

</details>

#### builds the LLVM kernel

- Verify: builds the LLVM kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_JS_RUNTIME_BROWSER_STATE-001
step("Verify: builds the LLVM kernel")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_runtime_probe_build("llvm")
```

</details>

#### boots the Cranelift guest and reaches the success marker

- Verify: boots the Cranelift guest and reaches the success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_JS_RUNTIME_BROWSER_STATE-001
step("Verify: boots the Cranelift guest and reaches the success marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_runtime_probe_boot("cranelift")
```

</details>

#### boots the LLVM guest and reaches the success marker

- Verify: boots the LLVM guest and reaches the success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_JS_RUNTIME_BROWSER_STATE-001
step("Verify: boots the LLVM guest and reaches the success marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_runtime_probe_boot("llvm")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cfd0c06fc328085ce88b4a039e0bfc5314321b056be3f388d2df1bada5ad82e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cfd0c06fc328085ce88b4a039e0bfc5314321b056be3f388d2df1bada5ad82e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cfd0c06fc328085ce88b4a039e0bfc5314321b056be3f388d2df1bada5ad82e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/js_runtime_browser_state_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/js_runtime_browser_state_in_qemu_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/js_runtime_browser_state_in_qemu_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/js_runtime_browser_state_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/js_runtime_browser_state_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
