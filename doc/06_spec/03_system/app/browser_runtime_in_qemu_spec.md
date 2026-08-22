# browser_runtime_in_qemu_spec

> Verifies the browser runtime in qemu behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_runtime_in_qemu_spec

Verifies the browser runtime in qemu behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser_runtime_in_qemu_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser runtime in qemu behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Browser runtime in QEMU Simple OS guest

#### builds the browser runtime probe kernel with Cranelift

- Verify: builds the browser runtime probe kernel with Cranelift


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_BROWSER_RUNTIME_IN_QEMU-001
step("Verify: builds the browser runtime probe kernel with Cranelift")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_browser_runtime_build("cranelift")
```

</details>

#### builds the browser runtime probe kernel with LLVM

- Verify: builds the browser runtime probe kernel with LLVM


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_BROWSER_RUNTIME_IN_QEMU-001
step("Verify: builds the browser runtime probe kernel with LLVM")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_browser_runtime_build("llvm")
```

</details>

#### boots the Cranelift guest and reaches the browser runtime probe success marker

- Verify: boots the Cranelift guest and reaches the browser runtime probe success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_BROWSER_RUNTIME_IN_QEMU-001
step("Verify: boots the Cranelift guest and reaches the browser runtime probe success marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_browser_runtime_boot("cranelift")
```

</details>

#### boots the LLVM guest and reaches the browser runtime probe success marker

- Verify: boots the LLVM guest and reaches the browser runtime probe success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-APP_BROWSER_RUNTIME_IN_QEMU-001
step("Verify: boots the LLVM guest and reaches the browser runtime probe success marker")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
_assert_browser_runtime_boot("llvm")
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

- Canonical SPipe generation for source `82b312f1abeac6b7b18b53fd8d1836ae70af1dc977c574374257f9fdf7e06e4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82b312f1abeac6b7b18b53fd8d1836ae70af1dc977c574374257f9fdf7e06e4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82b312f1abeac6b7b18b53fd8d1836ae70af1dc977c574374257f9fdf7e06e4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser_runtime_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/browser_runtime_in_qemu_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser_runtime_in_qemu_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser_runtime_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser_runtime_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
