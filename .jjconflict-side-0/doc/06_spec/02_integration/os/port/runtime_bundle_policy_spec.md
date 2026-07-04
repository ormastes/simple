# Runtime Bundle Policy Specification

> <details>

<!-- sdn-diagram:id=runtime_bundle_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_bundle_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_bundle_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_bundle_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Bundle Policy Specification

## Scenarios

### runtime bundle policy

#### rejects hosted runtime bundles and preserves Simple/C lane names

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/app/io/cli_compile_part2.spl")
val rust_cli = file_read("src/compiler_rust/driver/src/cli/native_build.rs")
val rust_config = file_read("src/compiler_rust/compiler/src/pipeline/native_project/config.rs")
val rust_tools = file_read("src/compiler_rust/compiler/src/pipeline/native_project/tools.rs")
expect(src).to_contain("cli_runtime_bundle_is_rust_or_hosted")
expect(src).to_contain("was removed; use simple-core or core-c-bootstrap")
expect(src).to_contain("use simple-core or core-c-bootstrap")
expect(src).to_contain("normalized.push(\"simple-core\")")
expect(src).to_contain("normalized.push(\"core-c-bootstrap\")")
expect(src.contains("normalized.push(\"runtime\")")).to_equal(false)
expect(src.contains("normalized.push(\"--runtime-bundle=runtime\")")).to_equal(false)
expect(src.contains("normalized.push(\"hosted\")")).to_equal(false)
expect(src.contains("Runtime lane: auto, simple-core, core-c-bootstrap, rust-hosted")).to_equal(false)
expect(rust_cli).to_contain("was removed; use simple-core or core-c-bootstrap")
expect(rust_cli.contains("hosted-runtime)")).to_equal(false)
expect(rust_config).to_contain("removed Rust-hosted runtime bundles")
expect(rust_config.contains("NativeRuntimeLane::RustHosted")).to_equal(false)
expect(rust_tools.contains("src/compiler_rust/target/simple-core")).to_equal(false)
expect(rust_tools.contains("src/compiler_rust/target/debug/libsimple_native_all.a")).to_equal(false)
expect(rust_tools.contains("src/compiler_rust/target/debug/deps/libsimple_runtime.a")).to_equal(false)
expect(rust_tools.contains("SIMPLE_NATIVE_ALL_PATH")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/runtime_bundle_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- runtime bundle policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
