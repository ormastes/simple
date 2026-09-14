# Windows Tool Bug-Fix Campaign (2026-09-13)

Scope: `origin/main@c56dd5004af` (checked 2026-09-14). Make itf devhub
(Jira/Confluence Data Center + Cloud, Bitbucket Server 8.19), the t32/MCP
launchers, `simple test`, Caret, plugins, and the Windows native bootstrap
work on Windows. All PR/commit facts below were verified directly with
`gh pr view --json state,mergeCommit,headRefOid` and
`git merge-base --is-ancestor <sha> origin/main`; anything not independently
re-checked from source is marked `(reported, not independently verified)`.

## DONE (merged to `origin/main`)

| item | PR | branch | merge sha (verified ancestor of main) | merged (UTC) |
|---|---|---|---|---|
| itf Jira REST routing w/ token (no forced acli login) + deployment/auth config + `--acli`; Confluence DC (`/rest/api/content`) + wiki stack-overflow fix + `login --deployment/--auth`; Bitbucket Server 8.19 (`/rest/api/1.0`, custom url+port, Bearer PAT, curl transport); `std.http_client` `add_header` recursion fix + `send_request`; Windows PATHEXT/`.cmd` process resolve; `simple test` on Windows (exe lookup) + memoization; MCP launcher stderr→temp log + log pruning + jo* dedupe; t32_mcp_server/t32_lsp_mcp_server `.cmd` launchers + runtime fallback; Caret JIT fallback (http_core join), caret/cs dispatch, terminal recovery; seed `text.join` typing; native-build Windows fixes (self_exe, `\\?\` snapshot path, empty closure); plugin manifests + skill layout (23 plugins validate); docs | #924 | `work/tool-bug-fix` | `a7c3570d64f` | 2026-09-13 23:02:27Z |
| re-wire `check-bootstrap-stage3-receipt-autowire` | #942 | `work/fix-hygiene-gate` | `8d94a6a3d26` | 2026-09-13 21:07:15Z |
| Windows long-path AOT publish (rename through a long-path-safe helper) | #940 | `work/win-long-path-publish` | `f5342c3fb75` | 2026-09-13 23:02:25Z |
| `runtime_native.c` long-path bounded reader — missing half of #744 | #953 | `work/restore-long-path-reader` | `48b442991ad` | 2026-09-14 02:59:23Z |
| stop `backend_shell_tuple` misdetecting Windows under a stripped env | #941 | `work/win-native-link-cc` | `1369400e7a8` | 2026-09-13 23:02:22Z |
| `native_linking` uses `std.io_runtime.host_os`, not a disagreeing detector | #944 | `work/win-native-link-libargs` | `285a6910768` | 2026-09-13 23:02:19Z |
| `mir_target_context_provider` uses `std.io_runtime.host_os` | #945 | `work/win-mir-target-triple` | `cfa5d30fb8f` | 2026-09-13 19:44:07Z |
| `llvm_target.spl` uses `std.io_runtime.host_os` | #947 | `work/win-llvm-target-host-os` | `31213ebdebd` | 2026-09-13 20:25:15Z |
| consolidate `rt_platform_name` onto a single extern decl (shared host-OS detector) | #949 | `work/win-host-os-detector` | `70c86c12463` | 2026-09-13 23:02:16Z |
| gate rpath emission off for Windows in cc-fallback runtime args (no `-rpath` for MSVC link) | #950 | `work/win-no-rpath-msvc` | `8edcdf4f5fa` | 2026-09-13 22:00:48Z |

Every merge sha above was confirmed with
`git merge-base --is-ancestor <sha> origin/main` (all `ok`). The #924 content
list is the PR title/description as recorded by `gh`; the itemized bullet
breakdown inside it is `(reported, not independently verified line-by-line)`.

## IN PROGRESS

| item | branch | PR | verified state |
|---|---|---|---|
| itf Confluence multi-target gateway config, follow-on to #924 | `fix/devhub-confluence-config` | #990 (open) | `OPEN`, `mergeStateStatus=BLOCKED`, head sha `0f54ff9fbd4` (task brief cited tip `c98a2a5070f` — stale; tip has since moved, recorded here as verified) |
| MCP interpreter startup (12.8s) investigation + restore `env_platform_process_owner_spec` | `work/mcp-startup-and-platform-spec` | #991 (open) | `OPEN`, `mergeStateStatus=BLOCKED`, head sha `159b90a9856` |
| SCV inventory native-hash + streamed cold-init events | `work/scv-inventory-native-hash` | #992 (open) | `OPEN`, `mergeStateStatus=BLOCKED`, head sha `0504f659b70` |
| correct beta1 release blocker to the CI matrix gate (relates to `beta1_tag_cannot_bootstrap_on_windows`) | `work/beta1-release-gate-record` | #989 (open) | `OPEN`, `mergeStateStatus=BLOCKED`, head sha `fe463f74da9` |
| Windows bootstrap stage2 + seed deploy (third blocker being fixed) | — | none found | No branch on `origin` and no open/closed PR located — **unverified**, reported by the task brief only |
| salvage follow-up: `native-build` `split_whitespace`/inventory refresh, builtin-receiver method fallback, maybe selective-import resolver | `work/tool-bug-fix-followup` | none found | `git ls-remote --heads origin` has no matching ref — **local-only or not yet pushed, unverified** |
| seed JIT Windows segfault (app.\*/function-local use) | `work/seed-jit-windows-segfault` | none found | No matching remote ref — **unverified** (a local worktree carries this branch name, unpushed) |
| lowering error file location | `work/seed-lowering-error-location` | none found | No matching remote ref — **unverified** |

`#942` clobbering `#938` (from the task brief) could not be confirmed by PR
title alone — #938 is titled "fix(runtime): every span-returning SIMD kernel
was dead in native binaries", unrelated on its face — so that claim is
recorded as `(reported, not independently verified)` rather than fact.

## OPEN / KNOWN BUGS

All of the following bug docs were confirmed present on `origin/main` under
`doc/08_tracking/bug/`:

- [`seed_jit_app_module_function_call_segfaults_windows_2026-09-13.md`](../../../08_tracking/bug/seed_jit_app_module_function_call_segfaults_windows_2026-09-13.md)
- [`seed_jit_function_local_use_segfaults_2026-09-13.md`](../../../08_tracking/bug/seed_jit_function_local_use_segfaults_2026-09-13.md)
- [`selective_use_leaks_same_named_fn_2026-09-13.md`](../../../08_tracking/bug/selective_use_leaks_same_named_fn_2026-09-13.md)
- [`windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13.md`](../../../08_tracking/bug/windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13.md)
- [`seed_receiver_text_join_resolves_to_thread_join_optional_2026-09-13.md`](../../../08_tracking/bug/seed_receiver_text_join_resolves_to_thread_join_optional_2026-09-13.md)
- [`seed_jit_some_constructor_corrupts_value_2026-09-13.md`](../../../08_tracking/bug/seed_jit_some_constructor_corrupts_value_2026-09-13.md)
  (`str(x!)` half is `(reported as uncommitted, not independently verified)`)
- [`beta1_tag_cannot_bootstrap_on_windows_2026-09-14.md`](../../../08_tracking/bug/beta1_tag_cannot_bootstrap_on_windows_2026-09-14.md)
  (see #989 above, which targets this)

Other reported-but-unverified state:
- deployed Windows seed `bin/release/x86_64-pc-windows-msvc/simple.exe` is
  stale (2026-09-01) pending bootstrap deploy — `(reported, not independently
  verified this session)`
- `C:` drive near full, so bootstrap runs from `D:` — **independently
  confirmed this session**: attempting a plain-checkout worktree on `C:`
  while authoring this doc drove `C:` to `0` bytes free (`df -h /c` showed
  `100% Use%`) and aborted a `git checkout` with `No space left on device`;
  the doc worktree was moved to `D:` (717G free at the time) to finish this
  change.

## Lessons

- Shared-worktree agents clobbered each other's commit messages/hunks — use
  one worktree per agent.
- An `update-branch` merge commit on a PR breaks the 64-commit bounded-range
  gate — rebase instead of using GitHub's "Update branch" button.
- CI queue backlog delays required checks; budget for it when polling a merge
  loop.
- `C:` has essentially no free space campaign-wide — verified directly this
  session. Any new worktree or full checkout must go on `D:`, and sparse
  checkout (`git sparse-checkout init --cone` + `set <dir>`, never
  `git checkout <ref> -- .` which ignores sparse patterns and forces a full
  checkout) is required even there to keep doc-only changes cheap.

## Next steps

1. Land #990, #991, #992, #989 (all currently `BLOCKED` per `mergeStateStatus`
   — re-check required-check status before assuming they are close).
2. Locate or re-create the branches for the seed JIT Windows segfault fix,
   the lowering-error-location fix, and the `work/tool-bug-fix-followup`
   salvage work — none currently exist on `origin`.
3. Confirm/deny "Windows bootstrap stage2 + seed deploy" has an active
   branch; if it is only local to another worktree, get it pushed so it is
   tracked here.
4. Redeploy the Windows seed (`bin/release/x86_64-pc-windows-msvc/simple.exe`)
   once the above land, then re-verify the "stale seed" claim above.
5. Free real space on `C:` (it is at 0 bytes free, not merely "near full") —
   this now blocks routine worktree/checkout work on that drive, not only
   bootstrap.
6. Close out the open bug docs above as their fixes land, linking the landing
   PR into each bug doc.

## Progress log

- **2026-09-13**: #945 (19:44Z), #947 (20:25Z), #950 (22:00Z), #942 (21:07Z)
  merged. Then a cluster landed together at 23:02Z: #924, #940, #941, #944,
  #949 (all merged 2026-09-13T23:02:1x-2xZ).
- **2026-09-14**: #953 merged 02:59:23Z (missing half of #744, C runtime
  bounded reader). PRs #988, #989, #990, #991, #992 opened between
  ~04:45Z and 06:06Z, all currently `OPEN`/`BLOCKED`. This plan doc created
  and landed via `work/windows-tool-bugfix-plan-doc` (authored from a `D:`
  worktree after `C:` was found to have 0 bytes free).
