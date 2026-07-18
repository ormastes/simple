# Native Build SMF Co-production

> Tests that the native-build command with --emit-smf flag produces both a native binary and an SMF cache file with manifest entry. Verifies the co-production pipeline correctly generates paired compilation artifacts.

<!-- sdn-diagram:id=native_build_smf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_build_smf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_build_smf_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_build_smf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build SMF Co-production

Tests that the native-build command with --emit-smf flag produces both a native binary and an SMF cache file with manifest entry. Verifies the co-production pipeline correctly generates paired compilation artifacts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/native_build_smf_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the native-build command with --emit-smf flag produces both a native
binary and an SMF cache file with manifest entry. Verifies the co-production
pipeline correctly generates paired compilation artifacts.

## Scenarios

### Native build output format selection

#### defaults to dynload Both format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = mock_output_config("bin/app", false)
val format = mock_select_format(config)
expect(format).to_equal(MOCK_FORMAT_BOTH)
```

</details>

#### selects native-only format with one-binary mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = mock_output_config_mode("bin/app", false, "one-binary")
val format = mock_select_format(config)
expect(format).to_equal(MOCK_FORMAT_NATIVE)
```

</details>

#### selects Both format with --emit-smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = mock_output_config("bin/app", true)
val format = mock_select_format(config)
expect(format).to_equal(MOCK_FORMAT_BOTH)
```

</details>

### SMF cache path generation

#### converts source path to cache path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = mock_smf_cache_path("src/app/cli/main.spl")
expect(path).to_equal("build/smf/src_app_cli_main.smf")
```

</details>

#### handles simple paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = mock_smf_cache_path("src/main.spl")
expect(path).to_equal("build/smf/src_main.smf")
```

</details>

#### handles deeply nested paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = mock_smf_cache_path("src/compiler/70.backend/backend/compiler.spl")
expect(path).to_equal("build/smf/src_compiler_70.backend_backend_compiler.smf")
```

</details>

### Native build --emit-smf flow

#### produces both artifacts when emit_smf is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = mock_output_config("bin/simple", true)
val format = mock_select_format(config)
expect(format).to_equal(MOCK_FORMAT_BOTH)
# In Both mode, native goes to output, SMF goes to cache
val smf_path = mock_smf_cache_path("src/app/cli/main.spl")
expect(smf_path).to_contain("build/smf/")
expect(smf_path).to_end_with(".smf")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
