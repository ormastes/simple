# SimpleOS native performance campaign blocked by runtime admission

Status: **OPEN — release blocking**

## Defect

NFR-002/NFR-003 have a fail-closed contract and executable operation-count
fixtures, but this host has no receipt-admitted self-hosted Stage 4 Simple
runtime authorized to execute SSpec or benchmark entrypoints. The imported
Stage 2 artifact is compile/native-build only. Using the deployed Rust seed or
silently extending Stage 2 authority would create false performance evidence.

## Impact

TLS, SSH/SFTP, NVMe, filesystem metadata, and sequential-I/O campaigns remain
`BLOCKED`. No p50/p95/p99/max/RSS/CV or NFR budget PASS may be claimed.

## Resume

1. Produce and admit a self-hosted binary receipt that explicitly authorizes
   the `test` and `run` commands at the canonical release path.
2. Execute each command and campaign listed in
   `doc/09_report/simpleos_hot_path_performance_contract_2026-08-20.md` once.
3. Retain raw samples and all campaign identity hashes, then pass them through
   `simpleos_performance_admit`; missing/non-comparable data remains blocked.

Owner: SimpleOS bootstrap/runtime lane

Final reviewer: SimpleOS verification owner
