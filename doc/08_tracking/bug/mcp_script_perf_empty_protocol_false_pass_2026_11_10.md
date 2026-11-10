# MCP performance gate accepts empty protocol output

- ID: `mcp_script_perf_empty_protocol_false_pass_2026_11_10`
- Priority: P2
- Owner: `scripts/check/check-mcp-script-mode-perf.shs`
- Status: fix implemented; 17 executable contract controls passed; review pending.

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
JSON members, foreign IDs, error replies, partial frames and trailing garbage
are rejected. Validation happens after the sample end timestamp and therefore
does not enter the reported server latency. A failed command or invalid response
exits nonzero even when timing thresholds are advisory.

The executable regression invokes the production gate with controlled child
processes, including valid Unicode/reordered responses and malformed controls:

```text
python scripts/check/check-mcp-script-mode-perf-contract.py
```

Results and individual raw outputs are retained under
`build/test-artifacts/mcp-script-mode-perf-contract/` by default.

The Windows Git-sh/Python 3.13 run on 2026-11-10 completed with
`mcp_perf_contract_cases=17 failures=0` and exit zero. The original empty-output
case now exits one with `missing initialize or tools/list response`. Positive
empty-inventory and Unicode/reordered/notification controls remain accepted.
The direct environment/process guard reports PASS; no application or library
source changed. Shell syntax and patch whitespace checks passed, and the
tracked `doc/06_spec` tree contains zero executable `_spec.spl` files.

This repair qualifies the measurement gate only. It supplies no startup/RSS
measurement for the production server and does not close
`mcp_interpreter_startup_12s_2026-09-14` or admit a compiler/runtime.
