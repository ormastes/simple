# Release Beta System Test Plan

## Scope

Validate the operator flow from strict bootstrap receipts through full-CLI qualification, release checker contracts, non-macOS platform artifacts, production verification, and successful GitHub publication.

| Scenario | Requirements | Evidence |
|---|---|---|
| Strict bootstrap chain | REQ-001/002, NFR-001..004 | Stage logs, provenance, elapsed/max-RSS, exact Stage 4 hash |
| Release checker qualification | REQ-005/006, NFR-005/007 | focused positive and deliberate-red fixtures |
| Platform matrix | REQ-003/004 | Linux/FreeBSD/Windows receipts and artifacts |
| Verification | REQ-007/009 | core/MCP/LSP/whole-test/guards/manual receipts |
| GitHub publication | REQ-008/010 | successful workflow run bound to revision/tag |

Primary scenario is visible and step-based; negative/malformed receipt cases are folded. The aggregate checker self-test supplies deliberate-red calibration. The live release scenario remains red until every real receipt exists.

Commands:

```text
sh scripts/check/check-release-beta-readiness.shs --self-test
sh test/01_unit/scripts/release_checker_contract_test.shs
sh test/01_unit/scripts/release_platform_evidence_contract_test.shs
bin/simple test test/03_system/app/release/feature/release_beta_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/app/release/feature/release_beta_spec.spl --output doc/06_spec --no-index
```

Release evidence additionally requires the commands named in the final requirements and `AGENTS.md`; this scenario aggregates their receipts rather than rerunning them.

The functional diagnostic Stage 3 run is not performance evidence when HIR tracing is enabled. Resource admission uses one clean isolated run and rejects Stage 3 above 254 seconds or any strict stage above 24 GiB maximum RSS.
