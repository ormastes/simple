# Phase 4 timeout descendant integration hold

## Scope

The timeout ownership repair is commit `230460151f80a1f236e58889b30012aee827b34c`.
The reviewed scheduler run allocation repair was integrated as
`85b3c8f9c7c34c47042e0026318681cf03ba2583` before the combined test.

## Evidence

- Unchanged helper red: an acknowledged descendant launched by `run_logged`
  remained live after the outer supervisor returned `143`.
- Fixed helper green: the focused helper contract passed `run_logged`,
  `run_logged_append`, and `run_logged_with_input` using the real process group
  supervisor.
- Combined scheduler allocation contract: PASS.
- Combined `--scheduler-signal` contract: HOLD after the third focused cycle.
  All three acknowledged descendants and their recorded process groups were
  dead, the `run.pid.seq` directory was removed, and the 10 ms observation
  monitor did not create `signal-cleanup-order-violation`. This is sampled
  cleanup-order evidence rather than proof of every instant. Three empty fake
  concurrency owner directories remained, so the executable correctly returned
  failure. The later parent aggregate assertion was not reached.

Retained WSL fixture:
`/tmp/stage4-tooling-matrix-test.OWXkly`

Acknowledged descendant evidence:

| task | PID | PGID | final state |
|---|---:|---:|---|
| link_cli | 43524 | 41373 | no live process |
| link_mcp | 43791 | 41578 | no live process |
| link_lsp | 43923 | 41957 | no live process |

The scheduler directory retains only `identity-before`; no `run.*` directory
remains. The three empty fixture owner directories are under
`concurrency-active/`. They keep the combined command at FAIL/HOLD and are not
silently accepted as a pass.

## Stop condition

The three-cycle cap is reached. Do not rerun this combined fixture in this
session. Source review may proceed independently; Phase 4 admission remains
HOLD until a fresh session resolves or classifies the fixture-owner cleanup.
