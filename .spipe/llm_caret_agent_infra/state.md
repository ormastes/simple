# Lane: llm_caret_agent_infra — caret agent sessions/worktrees, infra access, suite health

Updated: 2026-08-25 (orchestrator session; subagents do the work, orchestrator reviews + lands)

## Goal (raw)
SPipe skill; manage agent sessions and worktrees; update caret suites; broadcast a command
to each pane; launch the caret suite and test it in a tmux window. Then: dev toolset over
that infra, caret suite health, more Modern-SSpec system tests, production level; mail /
wiki / file-server access from caret and from dev tools (MCP); bootstrap redeploy for the
5 blocked specs; PR (branch authorised by user 2026-08-25: `caret-devtools-2026-08-25`).

## Landed on origin/main (tip 8a35f6f2a3a + 34e699280a0 local)
| slice | evidence | commit |
|---|---|---|
| agent_workspace (tmux private socket + git worktree --detach) | unit 6/6, cli 4/4, suite-in-tmux 1/1 | 7c1d460db39 |
| workspace CLI + recursion protection (depth env, own-pane skip) | workspace_cli_system 4/4 | 7c1d460db39 |
| shell recursion guard `scripts/lib/recursion_guard.shs` (+4 scripts) | selftest 4 fixtures, spec 2/2, ~56 µs | e2ff76d5947 |
| honest detach/attach/worktree_add + 3 system specs | team 1/1, recovery 7/7, parity 1/1 | d1a00f97bf0 |
| suite triage: 6 specs repaired, 6 defects filed | 43/60 → 62/67 on origin-tip seed | 039b7ca07e4 |
| infra tools mail/storage + permission gating | infra_tools 17/17, tools 37/37 | ff96cb20fed |
| live Docker evidence wrapper (MinIO + greenmail) | `PASS — 2 live row(s)` x2 | 43cbb826621 |
| std fixes: json contracts, serializer, utf8, tui input, pure_sql, smtp, json_helpers | each with reproduce+similar specs | 9fb6d5e92cb c2fe4e7a88e 0b260656e7a a0a47e21e8a 9c38cc83e86 d75f47c152c 7a24dab0e94 |
| `}}` reclassified as documented escape; pinned in both frontends | 11/11, 5/5 | 34e699280a0 (local) |

## In flight (subagents, disjoint files)
| lane | owner files | status |
|---|---|---|
| bootstrap redeploy → 5 blocked specs | bin/release deploy, cached caret artifact, `.spipe/bootstrap-*` | running; riding lane-bootstrap-s4's Stage 3/4 |
| wiki tools + MCP `caret_*` group | infra_wiki.spl, tools.spl, config.spl, src/app/mcp/main_lazy_caret_tools.spl | running |
| mail hardening: STARTTLS, RFC3501 FETCH parser, read timeouts | imap/*, smtp/*, io/tls_sffi.spl, infra_mail.spl | running |
| name-keyed co-compiled registry → (module, name) | src/compiler_rust module_loader.rs, self-hosted resolver | running |

## Plan (remaining, in order)
1. Review each in-flight report: diff vs origin AND HEAD per file, mirror check, orchestrator rerun at bracketed binary identity. Commit by explicit pathspec.
2. Push branch `caret-devtools-2026-08-25` from a temp worktree; open PR via `gh` (user override of no-branches rule, 2026-08-25).
3. Full 67-spec caret census on the redeployed binary from a clean origin-tip worktree; publish before/after.
4. Production verdict per gap below; anything still open gets a bug record with owner + unblock condition.

## Gap ledger (production-level = all rows closed or explicitly accepted)
| # | gap | status | unblock condition / owner |
|---|---|---|---|
| G1 | All evidence on the Rust SEED, not the self-hosted binary | OPEN | blocked deeper than expected: Stage 3/4 are planner-receipt-gated (simple-bootstrap-planner-admission-v2, 28 bound keys, exit 64 without). Bootstrap chain running; then rerun the 67-spec census |
| G2 | 5 specs env-blocked (cli_cached, cli_hidden_cached, native_closure, tui_pty, messaging_phase_cli) | OPEN | needs a Stage 4 CLI. Stage 2 now BUILDS clean (757 compiled, 0 failed) with the timeout fix but is rejected `sanity FAIL - frontend smoke exited 2` — a genuine smoke error, NOT the old budget clamp (that was exit 1). Next move: hand-replay candidate_frontend_smoke against build/bootstrap/s4chain/stage2/x86_64-unknown-linux-gnu/simple.rejected (sha 38793867…) capturing stderr, which the wrapper discards |
| G3 | Deployed seed cannot parse origin stdlib (`unsafe(...)`) | **CLOSED 2026-08-25** | seed redeployed 05:16 (60641352, sha 706fa636…); orchestrator probe printed the value |
| G4 | No STARTTLS (587/143) | **PARTIAL** — negotiation shipped, transport BLOCKED | no fd-upgrade extern exists anywhere; `rt_tls_client_from_fd` designed in tls_no_fd_upgrade_blocks_starttls_2026-08-25; runtime lane |
| G5 | IMAP FETCH via lenient line scanner; no `UID FETCH` | **CLOSED 2026-08-25** | RFC 3501 parser + literal-aware framer + builder; fetch_parse 9/9, sabotage-proven |
| G6 | No read timeout on the mail path | **CLOSED 2026-08-25** | tls_read_timeout facade + monotonic deadlines; timeout spec 3/3, wall < 5 s |
| G7 | FTP storage backend unbacked (`rt_ftp_*`) | ACCEPTED-BLOCKED | runtime lane backs it, or a pure-Simple FTP client over io.tcp is requested |
| G8 | Wiki access; caret tools unreachable from dev tools | **CLOSED 2026-08-25** | infra_wiki (Confluence + local md) + 9 confirm-gated MCP `caret_*` tools; stdio spec 3/3; startup +1 module |
| G9 | Name-keyed co-compiled function registry (silent shadowing) | OPEN → agent | (module,name) keyed registry in both compilers; sabotage specs |
| G10 | `}}` in literals | CLOSED | documented brace escape; pinned in both frontends |
| G11 | pure_sql reopen of checkpointed `TEXT NOT NULL` overflows | OPEN, filed | pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25; DB lane |
| G12 | json_serialize sorts keys (by design) | ACCEPTED | order-insensitive assertions only |
| G13 | Live infra evidence needs a Docker host | ACCEPTED | CI runner with Docker |
| G14 | LSP code-action emitter must emit `}}}}`/concatenate | OPEN, needs record | IDE lane |
| G16 | Tracked stage binaries SEGV (advisory guard RED) | OPEN, pre-existing | bootstrap lane; guard promotes to mandatory after redeploy |
| G17 | Seed 05:16 could not parse easy_fix/accessor_rewrite.spl | **CLOSED 2026-08-25** | root cause: expression-position unsafe-block rule accepted a bare colon, so an identifier named unsafe/danger ate its block header. Fixed + rebuilt + DEPLOYED 06:08 (60646096, sha 3ef64bff…); cargo test 8/8, doctest 1/1, regression specs green |
| G18 | MCP core tool set serves 3 tools, specs pin 20 (pre-existing at origin) | OPEN, filed | mcp_core_tool_set_has_3_tools_spec_expects_20_2026-08-25 |
| G19 | Seeds have been built from UNCOMMITTED trees (the 05:16 deploy came from a scratch worktree carrying an unlanded parser hunk) | OPEN, needs record | require a git-clean, origin-pinned source for any deployed binary; check-seed-builds-push could bind the deployed sha to a commit |
| G20 | caret wiki_write appends .md, wiki_read does not — a page cannot be read back by the id used to write it | OPEN, filed | llm_caret_wiki_write_read_id_asymmetry_2026-08-25; one normalisation fn owned by write/read/search |
| G21 | doc/08_tracking/todo/todo_db.sdn regenerates to 277 rows against origin's 741 — a full-tree scan from this worktree would delete 464 tracked rows | OPEN, needs owner | establish which tree is authoritative for todo-scan before regenerating; this session deliberately did NOT commit the regenerated db |

## Rejected shortcuts (do not retry)
- Subagent stripped spec docstrings/@req/step() while "fixing one line" (2x) — restore origin spec, re-apply hunk only.
- Committing shared-tree files origin has moved past — rebuild from origin + hunk.
- `--3way` git apply on this shared index — fails; plain `git apply`.
- Running any new bootstrap while lane-bootstrap-s4 is in flight — ride it.
