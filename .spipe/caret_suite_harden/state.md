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

## Update 2026-10-31 (release/1.0.0 sweep, Windows 11)

**Evidence is Rust-seed only.** No self-hosted Windows binary exists on this host; Stage 4 is the bootstrap lane's (PR #5540). Binary: seed built from this branch, sha256 `c68209e1de31f314`. This is not release-grade PASS.

Caret + smux sweep of 187 specs, run one at a time:

| Run | Seed | Passed | Failed | Other |
|---|---|---|---|---|
| Start | tracked `bin/simple.exe` (95 seed commits behind) | 127 | 51 | 6 broken, 3 could-not-complete |
| End | built from this branch | 160 | 22 | 4 pending-only, 1 timed out |

The old seed counted pending-only specs as passes, so the start figure is inflated by 4.

Still RED, each with a named cause (records: `doc/08_tracking/bug/caret_system_specs_windows_red_2026-10-31.md`, `smux_native_provider_lane_blocked_on_windows_seed_2026-10-31.md`, `smux_live_pty_multi_pane_needs_native_resize_2026-10-31.md`, `bin_caret_dropped_native_only_launcher_policy_2026-09-06.md`):

- Owner declined the native-only `bin/caret` policy: `caret_launcher_policy_spec`, `llm_caret_cli_hardening_spec`. Left RED on purpose.
- No native build on this host (seed `native-build` panics in vendored cranelift; no Stage 4): `smux_{configured_launch,literal_input,presentation_native,window_rename,windows_conpty_features,windows_owner_lifecycle,windows_shared_clients,interactive_windows_input,zoom}`, `pane_backend`, `llm_caret_{cli_cached,cli_hidden_cached,native_closure,messaging_phase_cli}`.
- Missing host tools or services: tmux (`workspace_cli`, `workspace_recovery`), `script` (`tui_pty`), `pgrep` (`installed_claude_cli`), model root (`slang_local_hello`), framed endpoint config (`coremux_sosix_endpoint`).
- `cs_live_agents` timed out at the runner's 120s budget; live agents stopped at first-run prompts.

SUPERSEDES the 2026-10-03 "Open" note on `caret_workbench_e2e` seam 1: fixed by routing shebang scripts through the POSIX shell, now 2/2.

Known open: `to_int_nil_coalesce_dead_fallback_2026-10-31.md`; C and Rust `rt_bytes_to_text` disagree on malformed bytes; `bin/simple lint` crashes on several smux and caret files on both this branch and the base.
