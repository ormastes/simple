# mcp_lsp_nfr_evidence_contract_spec

> Purpose: the MCP/LSP NFR evidence gate is observed by EXECUTING it — its

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_lsp_nfr_evidence_contract_spec

Purpose: the MCP/LSP NFR evidence gate is observed by EXECUTING it — its

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/mcp_lsp_nfr_evidence_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: the MCP/LSP NFR evidence gate is observed by EXECUTING it — its
fail-closed configuration path and its production wrapper selection — instead
of grepping the script text. Audience: MCP/LSP operators who rely on
check-mcp-lsp-nfr-evidence.shs as a release gate.

## Scenarios

### MCP and LSP production NFR evidence contract

#### selects production wrapper binaries that exist on this host

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects production wrapper binaries that exist on this host
   - Expected: file_exists("bin/simple_mcp_server") is true
   - Expected: file_exists("bin/simple_lsp_mcp_server") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects production wrapper binaries that exist on this host")
# evidence(protocol_json): wrapper presence is the typed precondition for native evidence
expect(file_exists("bin/simple_mcp_server")).to_equal(true)
expect(file_exists("bin/simple_lsp_mcp_server")).to_equal(true)
```

</details>

#### fails closed on an invalid NFR sample count

- fails closed on an invalid NFR sample count
   - Expected: exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed on an invalid NFR sample count")
# evidence(protocol_json): exit code and marker are the complete typed oracle
val (stdout, stderr, exit_code) = process_run("/bin/sh", ["-c",
    "MCP_LSP_NFR_SAMPLES=0 sh scripts/check/check-mcp-lsp-nfr-evidence.shs"])
expect(exit_code).to_equal(2)  # oracle: gate exit code 2 = invalid configuration, per scripts/check/check-mcp-lsp-nfr-evidence.shs usage()
expect(stdout).to_contain("error=invalid_sample_count:0")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `078c50380eae3beab4034db4175e69617d108d6147b036f89cc496933836862c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `078c50380eae3beab4034db4175e69617d108d6147b036f89cc496933836862c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `078c50380eae3beab4034db4175e69617d108d6147b036f89cc496933836862c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/check/mcp_lsp_nfr_evidence_contract_spec.spl
mirror: doc/06_spec/03_system/check/mcp_lsp_nfr_evidence_contract_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/mcp_lsp_nfr_evidence_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/mcp_lsp_nfr_evidence_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
