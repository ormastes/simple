# Lane state — caret_suite_harden

**Goal (2026-10-03, Windows host).** Harden the caret suite: (1) smux works on
Windows and caret uses it; (2) caret dashboard and the agent screen share one
window, left and right; (3) the Claude wrapper starts and works from dashboard
input — then Codex and Kimi; (4) a very small local model runs through slang
and answers "hello" like Claude. Real launch tests, Modern SSpec.

Runtime: phase-1 seed built from this branch's source
(`build/p1-target/x86_64-pc-windows-msvc/bootstrap/simple.exe`, no llvm
feature). All evidence below is from that binary on Windows 11.

## Acceptance criteria

| AC | State | Evidence |
|---|---|---|
| AC-1 smux on Windows | DONE | `smux_terminal_service_spec` 8/8 (was 5/8), `smux_api_spec` 5/5, `smux_app_spec` 5/5, `smux_pty_controlling_terminal_spec` 2/2 (ConPTY row: `mode con` reports pane 31x97, pipe reports host console), `vt_screen_spec` 7/7, `smux_client` protocol round-trip |
| AC-1b caret uses smux | DONE | `pane_backend_spec` 14/14 incl. live smux pane computing 4711*3 |
| AC-2 left/right split | DONE | `cs_dashboard_spec` split + narrow scenarios; real `cs_main.spl` run shows roster left, Claude screen right |
| AC-3 claude via dashboard | DONE | `cs_live_agents_system_spec` Claude 14133; real `cs` stdin run |
| AC-3b codex, kimi | DONE | same spec, Codex and Kimi scenarios green |
| AC-4 slang small model hello | DONE (1.5B) | `caret_slang_local_hello_system_spec` 3/3 with Qwen2.5-1.5B-Instruct Q4_K_M; 0.5B fails the hello oracle (sabotage-verified) — bug filed |
| AC-5 sspec mirrors | DONE | `spipe-docgen` mirrors for every new/changed spec, 0 stubs, 0 warnings |

Perf: `cs_refresh` + `cs_render` (140x40) while Claude streams: 18 ms avg, 46 ms
worst over 20 refreshes (interpreter, phase 1). Windows slang memory probe adds
~2.4 s per model load (PowerShell CIM, two probes).

Sabotage: hello oracle red with 0.5B; live oracle red with a wrong expected
product; interpreter regression spec red on the pre-fix seed (0 vs 3/1).

## Open (not in this lane's ACs)

- `caret_workbench_e2e_spec` seam 1: manager spawns `agent_stub.shs` directly;
  Windows cannot exec it (`ProcessLifecycle::Lost`). Pre-existing.
- `cpu -  rss -` on Windows: `sosix_proc_usage` has no Windows reader.
- GGUF chat template: `doc/08_tracking/bug/caret_slang_local_ignores_gguf_chat_template_2026-10-03.md`.
- The repo's deployed Windows seeds are stale; `bin/cs.cmd` needs a phase-1
  redeploy from this source to pick up the seed fixes.
