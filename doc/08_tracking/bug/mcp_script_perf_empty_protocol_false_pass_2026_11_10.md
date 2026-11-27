# MCP performance gate accepts empty protocol output

- ID: `mcp_script_perf_empty_protocol_false_pass_2026_11_10`
- Priority: P2
- Owner: `scripts/check/check-mcp-script-mode-perf.shs`
- Status: FIXED (2026-11-27) — source repair landed in `1305f6bf618` and `e3a09a382d5`; live-verified 18/18 contract controls on `release/1.0.0`.

## Reproduction

At release source `6d496f82c5acabc2fc52b2b78146272e664dc371`, execute
the performance gate with `RUNS=1` from a fixture directory containing
`bin/simple_mcp_server` and `bin/simple_lsp_mcp_server` that both exit zero
without writing stdout. The real gate reported:

```text
python3_mcp_median_ms=1053
simple_mcp_script_median_ms=789
simple_lsp_mcp_script_median_ms=183
mcp_script_perf_status=pass
```

Exit status was zero. These timings describe empty fixture processes, not
working MCP servers. The gate checked only process exit and elapsed time.
Its nonzero-command path also returned a numeric sentinel as success, allowing
unavailable baselines or advisory mode to obscure failed execution.

## Repair and acceptance

Each timed sample must produce complete byte-counted Content-Length frames.
Both requested string IDs (`1` initialize and `2` tools/list) must appear once
as successful JSON-RPC 2.0 responses with the required result shapes. Replies
may arrive in either order and valid notifications may appear between them.
An empty tools array is valid; an absent or malformed array is not. Duplicate
JSON members, nonfinite JSON constants, foreign IDs, error replies, partial
frames and trailing garbage are rejected. Validation happens after the sample end timestamp and therefore
does not enter the reported server latency. A failed command or invalid response
exits nonzero even when timing thresholds are advisory.

The executable regression invokes the production gate with controlled child
processes, including valid Unicode/reordered responses and malformed controls:

```text
python scripts/check/check-mcp-script-mode-perf-contract.py [deleted 2026-11-26]
```

Results and individual raw outputs are retained under
`build/test-artifacts/mcp-script-mode-perf-contract/` by default.

The Windows Git-sh/Python 3.13 run on 2026-11-10 completed with
`mcp_perf_contract_cases=17 failures=0` and exit zero. The original empty-output
case now exits one with `missing initialize or tools/list response`. Positive
empty-inventory and Unicode/reordered/notification controls remain accepted.
Independent review found that the duplicate-member fixture originally had an
incorrect frame length and that Python's default JSON parser accepted NaN.
The fixture now computes its byte length after inserting the duplicate member;
the parser rejects nonfinite JSON constants explicitly. Both affected controls
passed (`mcp_perf_contract_cases=2 failures=0`), with assertions checking the
specific duplicate-member and nonfinite diagnostics. The other 16 unchanged
controls retain their initial passing evidence. Together these cover 18 cases.
The direct environment/process guard reports PASS; no application or library
source changed. Shell syntax and patch whitespace checks passed, and the
tracked `doc/06_spec` tree contains zero executable `_spec.spl` files.

This repair qualifies the measurement gate only. It supplies no startup/RSS
measurement for the production server and does not close
`mcp_interpreter_startup_12s_2026-09-14` or admit a compiler/runtime.

## Live Verification on `release/1.0.0` (2026-11-27, lane `w3-2-scripts-specs-hygiene`)

- **Landed fix commits (ancestors of base `74713fbd005`):**
  - `1305f6bf618` (`fix(mcp): reject invalid protocol samples in performance gate`)
  - `e3a09a382d5` (`fix(mcp): reject nonfinite JSON and strengthen protocol controls`)
- **Live regression re-run against `scripts/check/check-mcp-script-mode-perf.shs`:**
  - `scripts/check/check-mcp-script-mode-perf-contract.py` was removed on 2026-11-26 in `02cd694e250`; extracted `02cd694e250^:scripts/check/check-mcp-script-mode-perf-contract.py` outside the worktree and executed it with Python 3.13 directly against the worktree's `scripts/check/check-mcp-script-mode-perf.shs` on Windows.
  - Exited `0` with `mcp_perf_contract_cases=18 failures=0` (all 18 controls PASS: `valid_valid`, `unicode_valid`, `empty_valid`, `missing_valid`, `foreign_valid`, `duplicate_valid`, `error_valid`, `invalid_init_valid`, `invalid_tools_valid`, `invalid_tool_valid`, `numeric_id_valid`, `wrong_length_valid`, `truncated_valid`, `trailing_valid`, `duplicate_member_valid`, `nonfinite_valid`, `nonzero_valid`, `valid_empty`).
- **Tracking closure:** Updated `doc/08_tracking/bug/db/mcp_script_perf_empty_protocol_false_pass_2026_11_10.sdn` (`status` -> `fixed`, `valid` -> `true`) and appended a `done` row to `bug_fix_claims` closing the stale `fixing` claim (`01a1c3cc/app_services`).
