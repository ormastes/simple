# Simplebox Artifact Contract Specification

> Tests covering filesystem-launched simplebox admission contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simplebox Artifact Contract Specification

## Scenarios

### filesystem-launched simplebox admission contract

#### binds source entry applets and bounded file IO

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds source entry applets and bounded file IO
   - Expected: contract.schema_version equals `SIMPLEBOX_ARTIFACT_SCHEMA_V1`
   - Expected: contract.canonical_path equals `SIMPLEBOX_CANONICAL_PATH_V1`
   - Expected: contract.entry_source_owner equals `os.tools.simplebox.simplebox_main`
   - Expected: contract.entry_symbol equals `main`
   - Expected: contract.max_files equals `128`
   - Expected: contract.max_file_bytes equals `67108864`
   - Expected: contract.read_chunk_bytes equals `65536`
   - Expected: contract.requires_target_artifact is true
   - Expected: contract.requires_loader_authority_token is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("binds source entry applets and bounded file IO")
val contract = simplebox_artifact_contract_v1()
expect(contract.schema_version).to_equal(SIMPLEBOX_ARTIFACT_SCHEMA_V1)
expect(contract.canonical_path).to_equal(SIMPLEBOX_CANONICAL_PATH_V1)
expect(contract.entry_source_owner).to_equal("os.tools.simplebox.simplebox_main")
expect(contract.entry_symbol).to_equal("main")
expect(contract.applets).to_contain("cat")
expect(contract.applets).to_contain("head")
expect(contract.applets).to_contain("wc")
expect(contract.max_files).to_equal(128)
expect(contract.max_file_bytes).to_equal(67108864)
expect(contract.read_chunk_bytes).to_equal(65536)
expect(contract.requires_target_artifact).to_equal(true)
expect(contract.requires_loader_authority_token).to_equal(true)
```

</details>

#### uses the canonical dispatcher registry without artifact drift

- uses the canonical dispatcher registry without artifact drift
   - Expected: contract.applets equals `registry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses the canonical dispatcher registry without artifact drift")
val contract = simplebox_artifact_contract_v1()
val registry = simplebox_applet_names()
expect(contract.applets).to_equal(registry)
```

</details>

#### requires loader authority for canonical and applet filesystem paths

- requires loader authority for canonical and applet filesystem paths
   - Expected: simplebox_path_requires_loader_authority_v1("/bin/simplebox") is true
   - Expected: simplebox_path_requires_loader_authority_v1("/bin/./cat") is true
   - Expected: simplebox_path_requires_loader_authority_v1("/bin/head") is true
   - Expected: simplebox_path_requires_loader_authority_v1("/bin/wc") is true
   - Expected: primary_tool_path_requires_loader_authority_v1("/bin/seq") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires loader authority for canonical and applet filesystem paths")
expect(simplebox_path_requires_loader_authority_v1("/bin/simplebox")).to_equal(true)
expect(simplebox_path_requires_loader_authority_v1("/bin/./cat")).to_equal(true)
expect(simplebox_path_requires_loader_authority_v1("/bin/head")).to_equal(true)
expect(simplebox_path_requires_loader_authority_v1("/bin/wc")).to_equal(true)
expect(primary_tool_path_requires_loader_authority_v1("/bin/seq")).to_equal(true)
```

</details>

#### does not capture relative or unrelated executable paths

- does not capture relative or unrelated executable paths
   - Expected: simplebox_path_requires_loader_authority_v1("cat") is false
   - Expected: simplebox_path_requires_loader_authority_v1("/usr/bin/clang") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not capture relative or unrelated executable paths")
expect(simplebox_path_requires_loader_authority_v1("cat")).to_equal(false)
expect(simplebox_path_requires_loader_authority_v1("/usr/bin/clang")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tools/simplebox_artifact_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering filesystem-launched simplebox admission contract.
- filesystem-launched simplebox admission contract

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b316d589f35bc50488498b890145f8b0bb3d543589b3ee6d6354b01d2479261e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b316d589f35bc50488498b890145f8b0bb3d543589b3ee6d6354b01d2479261e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b316d589f35bc50488498b890145f8b0bb3d543589b3ee6d6354b01d2479261e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/tools/simplebox_artifact_contract_spec.spl
mirror: doc/06_spec/01_unit/os/tools/simplebox_artifact_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tools/simplebox_artifact_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tools/simplebox_artifact_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tools/simplebox_artifact_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tools/simplebox_artifact_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds source entry applets and bounded file IO' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_artifact_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the canonical dispatcher registry without artifact drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_artifact_contract_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires loader authority for canonical and applet filesystem paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
