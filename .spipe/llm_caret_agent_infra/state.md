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
| G1 | All evidence so far is on the Rust SEED, not the self-hosted binary | OPEN | redeploy lane lands Stage-4 CLI; rerun census (plan §3) |
| G2 | 5 specs env-blocked (cli_cached, cli_hidden_cached, native_closure, tui_pty, messaging_phase_cli) | OPEN | qualified cached caret artifact + SIMPLE_STAGE3/4_BINARY from the redeploy |
| G3 | Deployed seed cannot parse origin stdlib (`unsafe(...)`) | OPEN | same redeploy; bug record deployed_seed_cannot_parse_value_bound_unsafe_2026-08-25 |
| G4 | No STARTTLS (587/143) | OPEN → agent | fd-upgrade facade or honest runtime-gap record with extern design |
| G5 | IMAP FETCH parsed by lenient line scanner; no `UID FETCH` builder | OPEN → agent | RFC 3501 parser in imap/parse.spl + transcripts spec |
| G6 | No read timeout on TLS/TCP mail path (stalled server hangs tool) | OPEN → agent | bounded reads, `timed out after N ms` error, wall-time spec |
| G7 | FTP storage backend unbacked (`rt_ftp_*`, ftp_sffi.spl:17) | ACCEPTED-BLOCKED | runtime lane backs the extern or a pure-Simple FTP client over io.tcp is requested |
| G8 | Wiki access from caret; caret tools not reachable from dev tools | OPEN → agent | infra_wiki (Confluence + local md) + MCP `caret_*` lazy group with confirm gating |
| G9 | Name-keyed co-compiled function registry (silent shadowing by load order) | OPEN → agent | (module,name) keyed registry in seed + self-hosted; sabotage-proven specs |
| G10 | `}}` in literals | CLOSED (documented escape; pinned) | — |
| G11 | pure_sql reopen of checkpointed `TEXT NOT NULL` file stack-overflows | OPEN, filed | pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25; DB lane |
| G12 | json_serialize sorts keys (by design) — order-insensitive assertions only | ACCEPTED | — |
| G13 | Live infra evidence only on a Docker host (ERROR elsewhere by design) | ACCEPTED | CI runner with Docker |
| G14 | LSP code-action emitter must emit `}}}}` / concatenate | OPEN, needs record | IDE lane |
| G15 | Seed lexer name-collision diagnostic env-gated (`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION`) | folds into G9 | — |
| G16 | Tracked stage binaries SEGV (advisory guard RED) | OPEN, pre-existing | bootstrap lane; check-stage-binaries-runnable promotes to mandatory after redeploy |

## Rejected shortcuts (do not retry)
- Subagent stripped spec docstrings/@req/step() while "fixing one line" (2x) — restore origin spec, re-apply hunk only.
- Committing shared-tree files origin has moved past — rebuild from origin + hunk.
- `--3way` git apply on this shared index — fails; plain `git apply`.
- Running any new bootstrap while lane-bootstrap-s4 is in flight — ride it.
