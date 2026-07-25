# Compiler CompileOptions Field Access

> System-level regression check for FR-COMPILER-001. The driver CompileOptions

<!-- sdn-diagram:id=compiler_compile_options_field_access_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_compile_options_field_access_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_compile_options_field_access_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_compile_options_field_access_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler CompileOptions Field Access

System-level regression check for FR-COMPILER-001. The driver CompileOptions

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_compile_options_field_access_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System-level regression check for FR-COMPILER-001. The driver CompileOptions
type must expose driver-only fields after explicit import resolution.

## Scenarios

### compiler CompileOptions field access

#### reads driver-only fields from the explicitly imported CompileOptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
expect(opts.input_files.len()).to_equal(0)
expect(opts.low_memory).to_equal(false)
expect(opts.mode).to_equal(CompileMode.Jit)
```

</details>

#### does not resolve to backend CompileOptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = CompileOptions.default()
expect(opts.backend).to_equal("auto")
expect(opts.smf_output_mode).to_equal("code_only")
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
