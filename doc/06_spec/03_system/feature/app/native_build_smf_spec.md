# Native Build SMF Co-production

> Tests that the native-build command with --emit-smf flag produces both a native binary and an SMF cache file with manifest entry. Verifies the co-production pipeline correctly generates paired compilation artifacts.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the native-build command with --emit-smf flag produces both a native
binary and an SMF cache file with manifest entry. Verifies the co-production
pipeline correctly generates paired compilation artifacts.

## Scenarios

### Native build output format selection

#### defaults to dynload Both format

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to dynload Both format
   - Expected: format equals `MOCK_FORMAT_BOTH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults to dynload Both format")
val config = mock_output_config("bin/app", false)
val format = mock_select_format(config)
expect(format).to_equal(MOCK_FORMAT_BOTH)
```

</details>

#### selects native-only format with one-binary mode

- selects native-only format with one-binary mode
   - Expected: format equals `MOCK_FORMAT_NATIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects native-only format with one-binary mode")
val config = mock_output_config_mode("bin/app", false, "one-binary")
val format = mock_select_format(config)
expect(format).to_equal(MOCK_FORMAT_NATIVE)
```

</details>

#### selects Both format with --emit-smf

- selects Both format with --emit-smf
   - Expected: format equals `MOCK_FORMAT_BOTH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects Both format with --emit-smf")
val config = mock_output_config("bin/app", true)
val format = mock_select_format(config)
expect(format).to_equal(MOCK_FORMAT_BOTH)
```

</details>

### SMF cache path generation

#### converts source path to cache path

- converts source path to cache path
   - Expected: path equals `build/smf/src_app_cli_main.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts source path to cache path")
val path = mock_smf_cache_path("src/app/cli/main.spl")
expect(path).to_equal("build/smf/src_app_cli_main.smf")
```

</details>

#### handles simple paths

- handles simple paths
   - Expected: path equals `build/smf/src_main.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles simple paths")
val path = mock_smf_cache_path("src/main.spl")
expect(path).to_equal("build/smf/src_main.smf")
```

</details>

#### handles deeply nested paths

- handles deeply nested paths
   - Expected: path equals `build/smf/src_compiler_70.backend_backend_compiler.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles deeply nested paths")
val path = mock_smf_cache_path("src/compiler/70.backend/backend/compiler.spl")
expect(path).to_equal("build/smf/src_compiler_70.backend_backend_compiler.smf")
```

</details>

### Native build --emit-smf flow

#### produces both artifacts when emit_smf is true

- produces both artifacts when emit_smf is true
   - Expected: format equals `MOCK_FORMAT_BOTH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces both artifacts when emit_smf is true")
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
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca8dc06c14253c076a1b133481ea88f23b2984a3b547ce2ba5d9e73906e53a38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca8dc06c14253c076a1b133481ea88f23b2984a3b547ce2ba5d9e73906e53a38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca8dc06c14253c076a1b133481ea88f23b2984a3b547ce2ba5d9e73906e53a38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/native_build_smf_spec.spl
mirror: doc/06_spec/03_system/feature/app/native_build_smf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/native_build_smf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/native_build_smf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/native_build_smf_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to dynload Both format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/native_build_smf_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects native-only format with one-binary mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/native_build_smf_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects Both format with --emit-smf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
