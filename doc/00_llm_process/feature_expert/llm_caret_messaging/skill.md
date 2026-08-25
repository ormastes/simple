# LLM Caret Messaging Feature Expert

## Authority and boundaries

The primitive Simple room is the semantic authority. The messaging domain owns
identities, rooms, messages, receipts, tasks, artifacts, profiles, ACLs, audit,
and loop protection. `ChatTransportPort` adapts external chat; `AgentControlPort`
controls Claude, Codex, and Gemini. The adjacent agent-runtime launcher also
maps Kimi through `*_with_all`; do not misstate that as managed Kimi messaging
hook support. Provider protocol messages, agent launch
plans, legacy mailboxes, and SPipe documentation tooling remain separate.

No platform- or provider-specific type belongs in the domain. Capability levels
are `native`, `emulated`, `primitive_sidecar`, and `unsupported`. Fallback is
planned from capability data, not platform-name branches.

## Review invariants

- Typed canonical IDs and monotonic room sequence are preserved.
- Direct messages are ACL-protected rooms; private content never leaks publicly.
- Receipt state and evidence are separate and displayed truthfully.
- Context is bounded, chronological, deduplicated, redacted, ACL checked, and
  reproducible from a manifest of IDs and hashes.
- Injection is acknowledged before `consumed_by_agent` is recorded.
- Agent updates do not implicitly trigger agents; echo deduplication, hop limits,
  cooldowns, and terminal task states prevent loops.
- Inbound events deduplicate per binding and external ID. Outbound retries reuse
  the canonical message and idempotency key.
- Hooks enqueue locally and return promptly; credentials are secret references,
  never settings-file literals.
- Codex App Server is primary; Claude and Gemini lifecycle hooks map to the
  common agent-control contract.
- Bootstrap must-check runs the Caret local-model, four-provider wrapper, and
  primitive gates. Keep smux multi-Caret launch TODO until a production adapter
  actually connects smux supervision to the agent manager.

## SPipe evidence

Trace REQ-LLM-MSG-001 through REQ-LLM-MSG-017 to modern SSpec scenarios. Unit
evidence covers parsers, routing, context, receipts, fallback, and loop guards.
System evidence uses the real primitive server, SQLite, streaming path, and hook
commands. Simulators establish adapter contract behavior only; live platform
gates remain independently PASS, BLOCKED, or UNSUPPORTED.

The composite integration must keep `.codex`, `.agents`, `.claude`, and Gemini
command instructions semantically aligned. Installer tests must prove merge,
backup, hash ownership, safe uninstall, executable validation, MCP discovery,
and absence of embedded secrets.

## Agent-manager hardening (2026-08-16)

- `agent_runtime.spl` validates providers via `is_known_agent_provider`; an
  unknown provider is an `unknown_provider:<p>` error, never a silent claude
  fallback. Team launches suffix duplicate `agent_md_path` ids with `#<idx>`.
- `agent_plan.spl` drops caller extra_args starting with `--dangerously` and
  bare `--output-format` overrides.
- `agent_vcs.spl` filters Error/Warning/Hint banner lines from jj stdout;
  `agent_files.spl` marks unreadable files `unreadable:<path>` instead of an
  empty fingerprint that compares as "unchanged".
- `agent_discovery.spl` collects every `"name"`/`"identifier"` occurrence in a
  manifest (multi-server manifests no longer lose entries).
- Backend system evidence: `test/03_system/llm_caret_agent_backends_spec.spl`
  is a Modern SSpec scenario (docstring manual header, step() flow,
  @req REQ-LLM-CARET-BACKEND-001) exercising spawn/poll/kill for both the
  claude (`-p ... --output-format json`)
  and codex (`exec <prompt>`) argv contracts with a stub binary.

## Agent sessions and worktrees (2026-08-25)

`src/app/llm_caret/agent_workspace.spl` is the side-effecting counterpart of
the model-only `agent_tmux.spl` embed: one detached git worktree
(`<root>/<agent_id>`, never a branch) plus one tmux window per agent, on a
PRIVATE tmux socket (`tmux -L caret_ws_<id>`) so the operator's own tmux server
is never touched. `send_to_each_pane` broadcasts one command to every pane;
`launch_caret_suite` runs `bin/simple test <spec> --no-session-daemon` in a
`caret_suite` window and `wait_for_pane_text` polls `capture-pane` for the
authoritative `Results:` line. Worktree paths must be absolute (`git -C repo`
resolves relative paths against the repo). Evidence:
`test/01_unit/app/llm_caret/agent_workspace_spec.spl` (throwaway `git init`
fixture, two-pane broadcast with a per-pane marker oracle) and
`test/03_system/app/llm_caret/caret_suite_tmux_window_system_spec.spl`
(real suite run inside a tmux window). tmux absent => `pending("BLOCKED: ...")`,
never a silent pass.

### Workspace dev CLI + recursion protection (2026-08-25)

`bin/simple run src/app/llm_caret/main.spl workspace <id> <cmd> [--repo P] [--root P]`
(`src/app/llm_caret/workspace_cli.spl`): `status | attach | detach | add |
remove | list | panes | send | broadcast | capture | wait | suite | kill`.
Exit 0 ok / 1 failed / 2 usage. Recursion protection: every spawned command
is prefixed `LLM_CARET_WORKSPACE_DEPTH=<n+1>`; `launch_caret_suite` refuses
with `recursion_limit` at depth >= 1, and `send_to_each_pane` skips the pane
the process runs in (`TMUX_PANE`). Evidence:
`test/03_system/app/llm_caret/workspace_cli_system_spec.spl` (real CLI child
processes: 3-agent team, worktree isolation, broadcast, nested-suite refusal).

### Infra tools + suite health (2026-08-25)

Tools `mail_list/mail_read/mail_send` (std imap/smtp over io.tcp/tls_sffi)
and `storage_ls/get/put` (pure-Simple SigV4 MinIO adapter; ftp refuses —
`rt_ftp_*` unbacked) live in `infra_mail.spl`/`infra_storage.spl`, gated by
the tools.spl permission policy (send/put are mutating). Live proof:
`sh scripts/check/check-llm-caret-infra-live.shs` (Docker MinIO + greenmail,
~10 s, `PASS — 2 live row(s)`), reproduced by two independent runs.

The deployed 2026-08-23 seed cannot parse origin's stdlib (value-bound
`unsafe(...)`); caret evidence on origin content comes from a clean worktree
with a seed built from origin's `src/compiler_rust`. Defects fixed from that
census: json accessor return contracts, json_serialize `42.0`, utf8
`char_from_code` stub shadowing string_core, tui input cursor bytes vs
codepoints, pure_sql SELECT cache not invalidated by INSERT, smtp bodyless
forward declarations, json_helpers shadowed by std.mcp.helpers, `}}`
fixtures in claude_cli_spec. Still environment-blocked: cli_cached,
cli_hidden_cached, native_closure, tui_pty, messaging_phase_cli (need a
cached self-hosted artifact / stage binaries).

Mail hardening (2026-08-25): the three recorded production gaps are closed or
honestly filed. (1) IMAP FETCH replies are parsed by the literal-aware RFC
3501 parser in `std.nogc_sync_mut.imap.parse` (`imap_response_complete` frames
by `{N}` byte count on BOTH transports; `imap_parse_fetch_response` returns
typed items; `imap_build_uid_fetch` added), spec
`test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl` (sabotage-verified).
(2) Every mail read is deadline-bounded (`tls_read_timeout` facade over the
already-backed `rt_tls_client_read_timeout`; error
`mail server timed out after N ms`), spec
`test/01_unit/app/llm_caret/infra_mail_timeout_spec.spl` (silent listener,
2 s budget, wall < 5 s). (3) STARTTLS negotiation is fully implemented as a
transport-free state machine (`infra_mail_starttls.spl`, transcript spec
`infra_mail_starttls_spec.spl`), but the socket upgrade stays refused: no
runtime `rt_tls_client_from_fd` exists — C-side design filed in
`doc/08_tracking/bug/tls_no_fd_upgrade_blocks_starttls_2026-08-25.md`; a live
STARTTLS wrapper row stays BLOCKED until the runtime lane backs it. The live
wrapper's classify_log now derives live rows as passed-skipped == 2 gated
rows, so extra permanently-BLOCKED rows (ftp + wiki) don't break PASS.
Lane state: `.spipe/llm_caret_mail_hardening/state.md`.
