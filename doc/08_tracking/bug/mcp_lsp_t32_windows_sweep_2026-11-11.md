# MCP / LSP / T32 Windows sweep on release/1.0.0: fixes, coverage, and one environment note

2026-11-11, Windows 11 interpreter lane, work branch off release/1.0.0.
Scope: src/app/mcp, src/app/simple_lsp_mcp, src/app/lsp, src/app/cmm_lsp,
src/app/mcp_t32, src/app/t32_mcp_server. Landed via PR (see git log);
this record lists every distinct defect and its outcome.

## Environment note (not code)

- `src/app/cmm_lsp`, `src/app/mcp_t32`, `src/app/t32_cli` (and many others:
  `.claude/commands/*`, `.codex/commands/*`, `.spipe/*`, `test/cert/**`,
  `bin/mail`, ...) are tracked git symlinks (mode 120000). A
  `core.symlinks=false` checkout degrades them to plain files containing the
  target path, and module resolution then fails (`app.cmm_lsp.*`,
  `app.mcp_t32.*` unresolved). `scripts/setup/materialize-symlinks-windows.shs`
  (also wired into `scripts/setup/setup.shs`, exit 0 verified) restores real
  NTFS junctions/symlinks. Until the tree is materialized, the cmm/t32 specs
  cannot run on Windows. Do NOT commit the materializer's worktree effects:
  for file targets it hard-links the real content, which differs from the
  index blob (the target path text).

## Fixed in this change

1. **cli_passthrough visibility** — `_cli_args_for_name` and
   `_effective_cli_timeout_s` (commented "Spec-facing alias") were private;
   made pub. cli_passthrough_spec 2/2.

2. **sosix boundary spec** — `api_tools_sosix_boundary_spec` asserted
   `sosix_dir_list` works on Windows; directory-listing admission is
   deliberately POSIX-only (`sosix_require_posix_text_provider`). Rewrote the
   example to pin the platform contract: POSIX lists, Windows the checked
   owner refuses. 3/3. (AUTHORED_UNEXECUTED, never run before.)

3. **MCP bootstrap EOF crash** — `input()` returns nil (not "") at EOF on the
   Windows runtime; `read_stdin_message` called `.ends_with` on nil after
   answering the last request and died with exit 1. Nil-guarded every read in
   main_optimized.spl, main.spl, main_lazy.spl, main_lazy_v2.spl. The
   optimized bootstrap now answers initialize and exits 0.

4. **bootstrap_optimized_launch_spec /tmp split** — the runtime file owner
   writes `/tmp` drive-rooted while the spec's POSIX shell redirects from the
   MSYS temp, so the frame file never reached the child. Moved the scratch
   file under `build/test-artifacts/`. Spec green.

5. **cmm lexer phantom trailing statement** — `split("\n")` on a
   newline-terminated source yields a phantom empty segment, which became an
   `EmptyLine` statement (source "A\nB\n" parsed as 3 statements). Drop exactly
   one trailing empty segment; interior blanks keep their EmptyLine.
   cmm_parser_facade_spec 3/3; new coverage spec
   `cmm_lexer_trailing_newline_spec.spl` (3 examples) pins the behavior.

6. **cmm_dialog_label_ref spec helper name** — the spec defined
   `dlr_dlr_list_has` but called `dlr_list_has` (11 examples failing).
   Renamed the definition. 14/14.

7. **simple_lsp_mcp bounded-owner wiring** (three repairs, one lane):
   - json_helpers.spl carried a dead UNBOUNDED `run_command_text`
     (`process_run`) contradicting the bounded-owner contract; deleted it.
   - `find_simple_binary` lost its cwd-independent repo discovery; restored
     the pinned `SIMPLE_LIB` derivation (`lib_dir… - 4 + "/bin/simple"`).
   - `run_lsp_query` never consulted the in-process adapter: restored
     in-proc-first routing (L9 G1) with the bounded child as fallback.
   - `lsp_note_command_start` was never called (the metrics module documented
     the bump but the call was lost); `run_command_text` now bumps it.
   lsp_command_bounded_spec 4/4, lsp_query_inproc_spec 8/8 (new
   member-decline example added).

8. **in-proc adapter member-access deferral** — the engine cores take a bare
   symbol; dotted positions (`recv.member`, `self.field`, chains) degraded to
   a repo-wide "not found" once run_lsp_query routed in-proc first. The
   adapter now detects a dot-left-of-symbol position and declines with
   `member_access_deferred_to_child`, so the child's receiver-aware resolver
   answers. lsp_member_definition_spec 7/7, lsp_forwarding_resolution_spec 7/7.
   (Without this, the in-proc routing regressed both specs.)

9. **t32 wrapper pins** — `mcp_t32_dispatch_wiring_spec` pinned bug-6-era
   `T32_MCP_FRONTEND` full/cold source wiring that the generated wrapper no
   longer contains (replaced by the cached-artifact-only native admission
   contract). Rewrote the three wrapper scenarios to pin the current
   contract: hash-validated `T32_MCP_NATIVE` admission, release-candidate
   scan, fail-closed refusal (exit 127, no raw-source fallback), including
   the spec's own header/troubleshooting text. 65/65.

10. **lsp unit sweep flakes** — the first full-dir run showed 7 failing specs
    under concurrent load; every one passed on individual clean re-runs with
    no code change (cross-run stderr interleaving in the shared log made the
    first diagnosis misleading). Final sweeps re-run clean.

## Extended sweep: smux + container + remaining mcp (same session)

11. **SDN strict parser byte/char desync (three sites)** — a canonical doc
    containing a raw multi-byte char (café) failed strict parsing:
    `sdn_decode_quoted_scalar_v1` compared a char-space cursor against the
    byte length; `StrictSdnReaderV1.quoted()` handed the decoder a
    char-indexed `substring` of a byte span; and key/bare-scalar/table-name
    extraction did the same, corrupting every later key (`[ersion:]`).
    Fixed the decoder with the empty-slice sentinel, bridged `quoted()` via
    the validated byte span, and added a `text_span` byte->text helper used
    by all span extractions. runtime_operation_codec_v2_spec 5/5; sdn unit
    dir 7/7; bisection probes cover utf8/escape/pipe/multi-item arrays.

12. **smux binding artifact store on Windows** —
    `runtime_binding_store_v3` failed twice: `file_mode_bits` was private to
    its module (made pub), and the POSIX 0o600 mode equality check can never
    hold on Windows (CRT chmod maps to a read-only attribute), so no artifact
    was ever published. chmod stays best-effort everywhere; the exact-bits
    check is POSIX-only (`platform_name() != "windows"`).
    runtime_binding_store_v3_spec 2/2.

13. **mcp stdio specs blocked on deployed binaries** — the remaining mcp
    unit failures (fileio_main, mcp_initialize_response,
    mcp_tool_call_symbols, mcp_static_tools_perf, mcp_tool_set,
    mcp_windows_path_and_crlf, native_handler_owner_binding,
    mcp_dynload_upgrade) all launch through `bin/simple.cmd` /
    `bin/simple_mcp_server` wrappers, which fail closed (127) without an
    admitted cached native artifact — none is built in this worktree. The
    same code paths answer correctly when run source-mode through the seed
    (verified: initialize + tools/list wire responses, exit 0). These specs
    need the bootstrap lane to deploy `bin/release/**`; recorded, not worked
    around.

14. **smux end-to-end program run** — real session/pane/child via
    `os.apps.smux.api`: spawned `/bin/sh -c 'while read l; do echo
    "GOT:$l"; done'`, sent a command, capture shows `GOT:hello-smux` after 8
    poll iterations. The smux service itself is healthy on Windows; the
    caret workbench e2e flake is the manager/orchestration layer (hook storm
    timing), not smux.

## Still blocked (environment, not code)

- `simple_lsp_mcp_stdio_spec` (7 examples), `mcp_stdio_integration_spec`
  (16), and `lsp_runtime_owner_spec` require NATIVE server binaries
  (`SIMPLE_LSP_MCP_TEST_BINARY`, `SIMPLE_MCP_TEST_BINARY`,
  `SIMPLE_LSP_TEST_BINARY`; the mcp spec defaults to the generated
  `bin/simple_mcp_server` wrapper, which refuses without an admitted
  artifact). `native-build` of the servers through the Rust seed on this
  loaded box exceeds 30 minutes per artifact; the build lane should produce
  these and the specs re-run then. The `check` subcommand is likewise gated
  on a deployed self-hosted binary ("no admitted cached self-hosted check
  worker artifact").
- `src/app/mcp/bootstrap/{main,main_lazy,main_lazy_v2}.spl` import
  `app.mcp.helpers` and fail as BARE entries (entry-root resolution); they
  are superseded by main_optimized.spl (the documented C19 fix) and only
  referenced by February 2026 design docs. The EOF repair above stands, but
  making the old bootstraps launchable again is a compiler entry-root lane
  item, not pursued here.
