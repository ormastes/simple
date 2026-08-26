# Mcp Lsp Nfr Evidence Contract Specification

> Tests covering MCP and LSP production NFR evidence contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Lsp Nfr Evidence Contract Specification

## Scenarios

### MCP and LSP production NFR evidence contract

#### uses only production wrappers and correlated warm calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses only production wrappers and correlated warm calls
   - Expected: source does not contain `"src/app/mcp/main.spl --mode") or source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses only production wrappers and correlated warm calls")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read("scripts/check/check-mcp-lsp-nfr-evidence.shs")
expect(source).to_contain("MCP_SERVER=\"${MCP_SERVER:-bin/simple_mcp_server}\"")
expect(source).to_contain("LSP_MCP_SERVER=\"${LSP_MCP_SERVER:-bin/simple_lsp_mcp_server}\"")
expect(source).to_contain("request_id=\"$label-request-$i\"")
expect(source).to_contain("wait_for_id \"$request_id\"")
expect(source).to_contain("simple_status")
expect(source).to_contain("lsp_symbols")
expect(source.contains("src/app/mcp/main.spl --mode") or source.contains("src/app/simple_lsp_mcp/main.spl --mode")).to_equal(false)
```

</details>

#### retains bounded p95 RSS and executable provenance

- retains bounded p95 RSS and executable provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retains bounded p95 RSS and executable provenance")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read("scripts/check/check-mcp-lsp-nfr-evidence.shs")
expect(source).to_contain("MCP_LSP_NFR_SAMPLES:-20")
expect(source).to_contain("MCP_LSP_NFR_STARTUP_MAX_MS:-1000")
expect(source).to_contain("MCP_LSP_NFR_REQUEST_P95_MAX_MS:-200")
expect(source).to_contain("MCP_LSP_NFR_RSS_MAX_KIB:-1048576")
expect(source).to_contain("rank=$(( (count * 95 + 99) / 100 ))")
expect(source).to_contain("/usr/bin/time -f %M")
expect(source).to_contain("startup wrapper=$label mode=native native=")
expect(source).to_contain("actual=\"$(hash_file \"$native\")\"")
expect(source).to_contain("native_sha256_sidecar_missing")
expect(source).to_contain("native_sha256_mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/mcp_lsp_nfr_evidence_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP and LSP production NFR evidence contract.
- MCP and LSP production NFR evidence contract

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

- Canonical SPipe generation for source `9441f704c63db34b7b6ffc846aae8ab8bc92b01221b184ba61c8dbe65cf9c073`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9441f704c63db34b7b6ffc846aae8ab8bc92b01221b184ba61c8dbe65cf9c073`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9441f704c63db34b7b6ffc846aae8ab8bc92b01221b184ba61c8dbe65cf9c073`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/mcp_lsp_nfr_evidence_contract_spec.spl
mirror: doc/06_spec/03_system/check/mcp_lsp_nfr_evidence_contract_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/check/mcp_lsp_nfr_evidence_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/mcp_lsp_nfr_evidence_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/mcp_lsp_nfr_evidence_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
