# Phase-2 product-queue residuals on release/1.0.0 (Windows seed lane)

Status: OPEN (disposition ledger for the specs that remain RED after the
2026-11-12 product-queue fix pass). Companion to
`doc/08_report/phase2_product_queue_disposition_20261112.md`.

## Fixed this pass (verified green in the lane worktree)

| Spec | Root cause | Fix |
|---|---|---|
| scv_db_page_store_it | `secure_temp_dir` backslash spelling vs canonical `/` identity checks | canonical spelling (file_ops) |
| scv_db_git_candidate_it | same + `path_absolute` spelling | same |
| scv_db_git_blob_it | same | same |
| scv_db_semantic_pages_it | same | same |
| scv_db_restricted_evidence_it | same | same |
| tooling/centralized_storage_roots | POSIX-only fake roots (`/users`, `/repo`) cannot host-resolve on Windows | honest skip-gate (2 examples) |
| scv_filebuffer_status | POSIX `/bin/sh` mktemp fixture + printf content | host-portable fixture |
| scv_db_offline_actor_it | SymbolicLink examples need admin/dev-mode | capability skip-gate |
| scv_db_local_store_it | same | capability skip-gate |
| scv_db_quarantine_store_it | same (inline PowerShell link) | capability skip-gate |
| simple_process_manager/spm_service | spec calls `AuthorityToken.public_none()` static; product aliased a module fn | static method added on the class |
| sj_daemon_mutual_exclusion | spec passed `SjClient` where the handler is required (SEGV-avoidance contract) + `jj`-dependent exit-0 examples on a jj-less host | `client.handler` call fix + jj capability skip-gates |
| scv_parser_lock | POSIX `/tmp` fixture + `/bin/sh` printf wasm bytes | host-portable fixture |

Root fixes: `secure_temp_dir_raw`/`path_absolute` return canonical
forward-slash spelling on Windows (matching `path_final_existing`/`dir_walk`,
per the `host_path.spl` contract); `_path_entry_observe` accepts Win32
error 0 as observed-absence (seed FFI clears last-error, see
`seed_ffi_clears_last_error_getlasterror_always_zero_2026-11-12.md`);
`scv_structural_publish_v1` creates its `syntax` object dir;
`atomic.spl` lock acquire fails fast on a missing lock parent and returns the
`break_stale` outcome.

## Remaining RED classes

1. **scv write-path child spin** — 19 specs, see
   `scv_db_write_path_child_spin_windows_seed_2026-11-12.md`. Deterministic
   100%-CPU spin on the mutation path; read paths clean. NOT skip-gated.
2. **evidence_store dangling-link semantics** — 11/12 pass; the last example
   expects `Err(SCVDB_EVIDENCE_UNAVAILABLE)` when deleting a dangling link,
   product returns `Ok(already_absent_synced)`. Owner decision needed on the
   intended contract (`never reports a dangling evidence link as an already
   absent deletion`).
3. **Seed-gap exact-output** (specs spawn `bin/simple` = seed, asserting
   stderr/stdout purity the seed banner breaks; expected green under the
   self-hosted binary): scv_dual_write, scv_fsck_strong,
   sspec_maintain_compatibility, scv_doctor (2/4), scv_format_version (1/3).
4. **Assertion/oracle drift after fixes** (real product behavior differs from
   pinned oracles; needs owner review per example): scv_git_settlement_transport
   (2/10), scv_shadow_replication (0/3), scv_rebuild_db (2/3).
5. **POSIX-shell harness + missing host tool**: scv_fault_injection
   (`/bin/sh` script + `scv` CLI + fault injection), scv_jj_mutating_adapter
   (`/bin/sh` + `jj` CLI absent on host). Porting + capability gates is a
   separate lane's worth of work; kept RED.
6. **Misc product/cli drift** (individual small classes): spipe_quality_lint
   (lint count 1 vs 0), dynsmf_autoload_policy (cli output), guest_isa_contract
   (exit 2), sspec_maintain_cli (JSON/SARIF), startup_argparse_mmap_perf
   (perf threshold on loaded host), test_runner_cached_discovery_prefix
   (symlink walk), web_stack_sample (DbValue rendering oracle),
   browser_h1_loopback_e2e, x25519mlkem768_web_browser_integration,
   production_gui_web_renderer_parity, ui_edit_cli,
   wine_process_session_plan_command, cranelift_cross_module_call_abi
   (compiler lane), simple_lsp_mcp_stdio (SIMPLE_LSP_MCP_TEST_BINARY
   qualification binary not set in this lane).
