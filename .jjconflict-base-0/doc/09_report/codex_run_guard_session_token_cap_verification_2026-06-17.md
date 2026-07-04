# codex-run-guard Session-Token Cap — Verification (2026-06-17)

Verification that the new live session-token cap added to
`scripts/check/codex-run-guard.shs` works and did **not** break codex launches.

## Change under test

Cap 4 (`CODEX_GUARD_MAX_SESSION_TOKENS`, default 50M): the watchdog kills the
codex process tree when its active rollout's `input_tokens` exceeds the
threshold. The active rollout is located via `/proc/<pid>/fd` over the guard's
own codex subtree, so it never reads or acts on a concurrent session's rollout.
`tree_active_rollout` returns 0 unconditionally because the script runs under
`set -eu` and the caller uses `var=$(...)` — a non-zero return would kill the
whole watchdog and silently disable every cap.

## Results — all pass

| Test | Method | Result |
| --- | --- | --- |
| Static syntax | `dash -n` + `sh -n` on the committed script | clean |
| Real launch smoke | `codex --version` via `bin/codex` → guard | guard logged `guard active (… max_session_tokens=50000000)`, ran `codex-cli 0.140.0`, exit 0 |
| T1: no false-kill | 6s stub, no rollout fd, poll=2s, only token cap enabled | watchdog ran the new branch ~3× over the empty-fd `return 0` path, did **not** kill the healthy stub; guard exit 0, stub completed normally |
| T2: cap fires | 30s stub holding a fake rollout (`input_tokens: 999999999`), cap=100, poll=2s | guard logged `SESSION-TOKEN CAP: … 999999999 >= 100 — killing codex tree`, killed the tree at 3s (before the 30s stub completed), exit 143, no orphan processes |

Tests used stub binaries — no real codex session or tokens were consumed, and the
pre-existing live codex session (running the guard version it launched with) was
unaffected. T1 also confirms the early-exit fix: the watchdog correctly starts
when only the token cap is enabled (wall-clock and RSS caps disabled).

## Conclusion

codex launches are unbroken: real codex resolves and execs through the guard,
healthy sessions run untouched, and the runaway backstop fires as designed.

Related: guard commit `49a7593` (`fix(codex-guard): add live session-token cap
for runaway poll-loops`); the runaway it backstops is the
`simple_web_browser_production_hardening` rollout `019e85dc` (1.72B input tokens
over 3 days, 2026-06-02→05).
