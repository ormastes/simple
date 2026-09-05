# Warning/Allow Root-Cause Cleanup Canary Spec

> Guards the enforcement wiring introduced by the warning/allow cleanup slice:

<!-- sdn-diagram:id=warning_allow_root_cause_cleanup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=warning_allow_root_cause_cleanup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

warning_allow_root_cause_cleanup_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=warning_allow_root_cause_cleanup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Warning/Allow Root-Cause Cleanup Canary Spec

Guards the enforcement wiring introduced by the warning/allow cleanup slice:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/warning_allow_root_cause_cleanup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Guards the enforcement wiring introduced by the warning/allow cleanup slice:
- Rust CI must target `src/compiler_rust`, not the removed legacy `rust/` tree.
- The strict Simple lint lane must stay required and must use `--deny-all`.
- The primitive sort runtime keeps the current explicit NEON threshold constants
  so the strict Rust lane compiles its tests before Clippy runs.

## Scenarios

### warning allow root-cause cleanup gate wiring
_Enforcement canaries for owned warning/allow cleanup lanes._

#### rust workflow targets src compiler_rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val workflow = rt_file_read_text(".github/workflows/rust-tests.yml")
expect(workflow.contains("src/compiler_rust")).to_equal(true)
expect(workflow.contains("working-directory: src/compiler_rust")).to_equal(true)
```

</details>

#### simple strict lint workflow exists and runs deny-all

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val workflow = rt_file_read_text(".github/workflows/simple-strict-lints.yml")
expect(workflow.contains("Strict Simple Lints")).to_equal(true)
expect(workflow.contains("--deny-all")).to_equal(true)
expect(workflow.contains("warning_allow_root_cause_cleanup_spec.spl")).to_equal(true)
```

</details>

#### primitive sort runtime defines the NEON threshold constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val runtime = rt_file_read_text("src/compiler_rust/runtime/src/value/primitive_sort.rs")
expect(runtime.contains("const NEON_I64_RADIX_MIN_LEN")).to_equal(true)
expect(runtime.contains("const NEON_F64_RADIX_MIN_LEN")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
