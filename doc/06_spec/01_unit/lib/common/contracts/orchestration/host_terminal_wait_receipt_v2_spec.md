# Pure terminal-wait receipt qualification V2

Status: **NOT_RUN** — synthetic pure observations; no provider or runtime suite
executed. Source:
`test/01_unit/lib/common/contracts/orchestration/host_terminal_wait_receipt_v2_spec.spl`.

| Scenario | Intended assertion |
| --- | --- |
| Complete receipt | Canonical full wait roundtrips and qualifies against exact expected execution/identity/op/provider/time; workload exit 17 is preserved distinctly from CLI success. |
| Wait-only qualification | Inspect/start, running phase, failed CLI and unknown negative workload exit reject as terminal-wait authority. |
| Correlation | Changed observation digest, regressed time, backend/engine mismatch and another scope reject. |
| Canonical bounds | Noncanonical newline/termination, source above 8 MiB and changed operation digest reject. |

The pure module imports no host owner, filesystem, native provider or capacity
state. Its validator checks facts against protected expected values; it does not
authenticate a caller-supplied receipt by itself. No PASS is claimed.
