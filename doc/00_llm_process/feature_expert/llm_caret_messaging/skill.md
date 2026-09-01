# LLM Caret Messaging Feature Expert

## Authority and boundaries

The primitive Simple room is the semantic authority. The messaging domain owns
identities, rooms, messages, receipts, tasks, artifacts, profiles, ACLs, audit,
and loop protection. `ChatTransportPort` adapts external chat; `AgentControlPort`
controls Claude, Codex, and Gemini. Provider protocol messages, agent launch
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

## What exists now (2026-08-25)

### Agent workspaces

`src/app/llm_caret/agent_workspace.spl` is the side-effecting counterpart of the
model-only `agent_tmux.spl` embed: one detached git worktree
(`<root>/<agent_id>`, **never a branch**) plus one tmux window per agent, on a
PRIVATE tmux socket (`tmux -L caret_ws_<id>`) so the operator's own tmux server
is never touched. `send_to_each_pane` broadcasts one command to every pane;
`launch_caret_suite` runs `bin/simple test <spec> --no-session-daemon` in a
`caret_suite` window and `wait_for_pane_text` polls `capture-pane` for the
authoritative `Results:` line. Worktree paths must be absolute — `git -C repo`
resolves relative paths against the repo, not the cwd.

Evidence: `test/01_unit/app/llm_caret/agent_workspace_spec.spl` (throwaway
`git init` fixture, two-pane broadcast with a per-pane marker oracle) and
`test/03_system/app/llm_caret/{caret_suite_tmux_window,agent_team_workspace,
workspace_recovery,workspace_embed_parity}_system_spec.spl`. tmux absent =>
`pending("BLOCKED: ...")`, never a silent pass.

### Workspace dev CLI + recursion protection

`bin/simple run src/app/llm_caret/main.spl workspace <id> <cmd> [--repo P] [--root P]`
(`src/app/llm_caret/workspace_cli.spl`): `status | attach | detach | add |
remove | list | panes | send | broadcast | capture | wait | suite | kill`.
Exit **0** ok / **1** ran-and-failed / **2** usage (bare id, `help`, unknown
command, missing positional). Only `add`/`remove`/`list` work without tmux.

Recursion protection is two independent mechanisms: every spawned command is
prefixed `LLM_CARET_WORKSPACE_DEPTH=<n+1>` and `launch_caret_suite` refuses with
`recursion_limit` at depth >= `MAX_DEPTH` (currently **1**); and
`send_to_each_pane` skips the pane the process itself runs in (`TMUX_PANE`).
The shell analogue is `scripts/lib/recursion_guard.shs` (`SIMPLE_SHS_DEPTH` /
`SIMPLE_SHS_MAX_DEPTH` default 3 / optional `SIMPLE_SHS_GUARD_CHAIN`, exit **3**
on refusal, ~56-74 us per source, wired into `land.shs`,
`check-seed-builds-push.shs`, `check-stage-binaries-runnable.shs`,
`lint-cached.shs`). Evidence:
`test/03_system/app/llm_caret/workspace_cli_system_spec.spl` (real CLI child
processes: 3-agent team, worktree isolation, broadcast, nested-suite refusal),
`test/01_unit/scripts/recursion_guard_spec.spl`.

### Infra tools: mail, storage, wiki

`infra_mail.spl` / `infra_storage.spl` / `infra_wiki.spl` hold all server-facing
code; `tools.spl` adds only schemas, dispatch arms and permission class. Nine
tools: `mail_list/mail_read/mail_send`, `storage_ls/get/put` (pure-Simple SigV4
MinIO adapter; ftp refuses — `rt_ftp_*` unbacked), `wiki_search/read/write`
(Confluence via the devhub adapter, or a `local` markdown dir). `mail_send`,
`storage_put` and `wiki_write` are mutating and denied by default. Credentials
are **env references only** (`secret_env`, `access_key_env`, `token_env`); an
unset secret names the variable, never a value.

Mail hardening: IMAP replies go through the literal-aware RFC 3501 parser in
`std.nogc_sync_mut.imap.parse` (`imap_response_complete` frames by `{N}` byte
count on BOTH transports, `imap_parse_fetch_response` returns typed items,
`imap_build_uid_fetch` added) — sabotage-verified in
`test/01_unit/lib/nogc_sync_mut/imap/fetch_parse_spec.spl`. Every read is
deadline-bounded (`tls_read_timeout` over the backed
`rt_tls_client_read_timeout`; error `mail server timed out after N ms`), spec
`infra_mail_timeout_spec.spl` (silent listener, 2 s budget, wall < 5 s).

Live proof: `sh scripts/check/check-llm-caret-infra-live.shs` (Docker MinIO +
greenmail, ~10 s, `PASS — 2 live row(s)`), reproduced by two independent runs.
Its `classify_log` derives live rows as `passed - skipped == 2` gated rows, so
extra permanently-BLOCKED rows (ftp, wiki) don't break PASS.

### MCP `caret_*` tools

All nine tools are exposed by `bin/simple_mcp_server` as `caret_*`. Handlers:
`src/app/mcp/main_lazy_caret_tools.spl`. Two load-bearing decisions: the
mutating three require `"confirm": true` in the arguments or the call returns an
`isError` result; and the server **never imports** the caret/devhub/imap module
graph (measured to double startup) — each call shells to the one-shot CLI
`simple run src/app/llm_caret/tool_cli.spl <tool> <input.json> [--allow]` as a
child, so MCP startup gains exactly one module. Config comes from
`$LLM_CARET_CONFIG`. Spec: `test/03_system/app/mcp/caret_tools_mcp_system_spec.spl`.

## Landmines (learned the hard way — do not relearn)

- **Spec docstrings are load-bearing and get silently stripped.** Twice a
  subagent "fixing one line" removed docstring/`@req`/`step()` structure from a
  spec. Restore the origin spec and re-apply only the intended hunk. Never
  hand-edit a spec you do not own.
- **The shared working tree is stale.** Origin has usually moved past it.
  Rebuild changes from origin content plus your hunk; committing a shared-tree
  file reverts other sessions. `git apply --3way` fails on this shared index —
  use plain `git apply`.
- **`{x}` and `}}` in literals.** `}}` is a *documented brace escape*, not a
  bug; it is now pinned in both frontends. Fixtures that assumed otherwise were
  wrong. The open follow-on is that the LSP code-action emitter must emit
  `}}}}` or concatenate (IDE lane).
- **Name-collision shadowing is silent.** A co-compiled function registry keyed
  by bare name let `utf8.char_from_code` shadow `string_core`'s and
  `json_helpers` shadow `std.mcp.helpers`. The fix is a `(module, name)`-keyed
  registry in both compilers; assume any bare-name lookup is suspect.
- **Bracket every measurement with binary identity.** The deployed binary
  changed twice on 2026-08-25 alone. Record
  `readlink -f bin/simple && stat -c '%s %y'` with any timing or census, or the
  number means nothing.
- **Never start a bootstrap while another lane's is in flight** — ride it.

## Gap ledger (source of truth: `.spipe/llm_caret_agent_infra/state.md`)

Numbering follows that ledger, which currently runs G1-G18 with **no G15**.

| # | gap | status | unblock condition |
|---|---|---|---|
| G1 | All evidence is on the Rust SEED, not the self-hosted binary | OPEN | Stage 4 CLI; then rerun the 67-spec census |
| G2 | 5 specs env-blocked (`cli_cached`, `cli_hidden_cached`, `native_closure`, `tui_pty`, `messaging_phase_cli`) | OPEN | qualified cached caret artifact + `SIMPLE_STAGE3/4_BINARY` |
| G3 | Deployed seed could not parse origin stdlib (`unsafe(...)`) | CLOSED 2026-08-25 | seed redeployed; parser accepts `unsafe`/`danger` as identifiers |
| G4 | No STARTTLS (587/143) | PARTIAL — negotiation shipped, transport BLOCKED | no fd-upgrade extern exists; `rt_tls_client_from_fd` designed in `tls_no_fd_upgrade_blocks_starttls_2026-08-25`; runtime lane |
| G5 | IMAP FETCH via lenient line scanner; no `UID FETCH` | CLOSED 2026-08-25 | RFC 3501 parser + literal-aware framer + builder |
| G6 | No read timeout on the mail path | CLOSED 2026-08-25 | `tls_read_timeout` facade + monotonic deadlines |
| G7 | FTP storage backend unbacked (`rt_ftp_*`) | ACCEPTED-BLOCKED | runtime lane backs it, or a pure-Simple FTP client over `io.tcp` |
| G8 | Wiki access; caret tools unreachable from dev tools | CLOSED 2026-08-25 | `infra_wiki` + 9 confirm-gated MCP `caret_*` tools |
| G9 | Name-keyed co-compiled function registry (silent shadowing) | OPEN | `(module, name)`-keyed registry in both compilers; sabotage specs |
| G10 | `}}` in literals | CLOSED | documented brace escape, pinned in both frontends |
| G11 | pure_sql reopen of checkpointed `TEXT NOT NULL` overflows | OPEN, filed | `pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25`; DB lane |
| G12 | `json_serialize` sorts keys (by design) | ACCEPTED | order-insensitive assertions only |
| G13 | Live infra evidence needs a Docker host | ACCEPTED | CI runner with Docker |
| G14 | LSP code-action emitter must emit `}}}}`/concatenate | OPEN, needs record | IDE lane |
| G16 | Tracked stage binaries SEGV (advisory guard RED) | OPEN, pre-existing | bootstrap lane; guard promotes to mandatory after redeploy |
| G17 | Seed cannot parse `easy_fix/accessor_rewrite.spl` (aborts md doctests, demotes JIT) | OPEN | fix-forward in `src/compiler_rust/parser`; deploy-or-rollback decision |
| G18 | MCP core tool set serves 3 tools, specs pin 20 (pre-existing at origin) | OPEN, filed | `mcp_core_tool_set_has_3_tools_spec_expects_20_2026-08-25` |

Operator guide: `doc/07_guide/app/llm_caret_usage.md` (its "Known limitations"
table is the user-facing projection of this ledger and must be kept consistent
with it). Lane state: `.spipe/llm_caret_agent_infra/state.md`,
`.spipe/llm_caret_mail_hardening/state.md`.
