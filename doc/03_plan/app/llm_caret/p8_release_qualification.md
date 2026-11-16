# LLM Caret P8 release qualification (release/1.0.0)

Date: 2026-11-17. Status: static part run; native part PENDING deployed
self-hosted binary (`bin/release/<triple>/simple`, not the Rust seed).

P8 = "Integration shell/audit" phase of
`doc/03_plan/agent_tasks/llm_caret_claude_cli_full_parity_impl_plan.md`
(lane P7-P8). No matrix row carries `phase=P8`; P8 is the whole-suite final
completion gate of that plan, applied to the release line.

## Static part (no native binary) — results 2026-11-17

| Gate | Result | Note |
|---|---|---|
| `sh scripts/check/check-llm-caret-full-parity-plan.shs` | FAIL (env) | needs `tmp/claude/claude-code-main/src` (untracked source evidence, 0 files on this host); matrices themselves present: 599 feature / 1902 file / 14119 symbol rows |
| `sh scripts/check/check-llm-caret-claude-cli-trace.shs` | FAIL | `missing_symbol_trace` rows, e.g. `src/app/llm_caret/main.spl` `_chat_frames`, `_server_policy`, `agent_run_status` — regenerate `doc/09_report/llm_caret_claude_cli_symbols.tsv` |
| `sh scripts/check/check-caret-suite-bootstrap.shs --self-test` | did not finish in 600 s on this host | re-run with the native binary |

## P8 runnable checklist (run once the native compiler is deployed)

Run from a clean `release/1.0.0` worktree root; every line must exit 0.

```sh
set -e
readlink -f bin/simple; bin/simple --version 2>&1 | head -2   # must NOT be the seed
[ -d tmp/claude/claude-code-main/src ]                         # parity source evidence
sh scripts/check/check-llm-caret-full-parity-plan.shs
sh scripts/check/check-llm-caret-claude-cli-trace.shs
sh scripts/check/check-llm-caret-full-parity-implementation.shs
sh scripts/check/check-caret-suite-bootstrap.shs --self-test
for g in local-torch provider-wrappers agent-primitives multi-manager; do
  sh scripts/check/check-caret-suite-bootstrap.shs --gate "$g"
done
sh scripts/check/check-llm-caret-acceptance.shs
sh scripts/check/check-llm-caret-phase4-cli-admission.shs
sh scripts/check/check-llm-caret-native-closure.shs
sh scripts/check/check-llm-caret-server-serves.shs
sh scripts/check/check-llm-caret-tui-pty.shs
```

Pass criteria (from the parity plan Final Completion Gate): no incomplete
matrix rows, all unit/system specs pass, generated manuals report `0 stubs`,
direct runtime/env guard passes, compact provider behavior still passes.
Record binary digest, source revision, host, command and exit status per gate.
