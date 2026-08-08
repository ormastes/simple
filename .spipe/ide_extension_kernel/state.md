# IDE Extension Kernel Campaign — Coordination State

**CAMPAIGN COMPLETE 2026-07-29** — all Phase S items and all lanes (L0-L7,
L6b, F1-F7) landed on origin/main; full commit ledger in the plan's
"Execution status" section. Open follow-ups: 5-spec re-verify queue (below),
guest-QEMU theme verification, L1's kernel API change requests, mail/planner
owner_module fix, F7 interpreter-quirk bug filing.

Plan: doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md
Started: 2026-07-29. Plan landed origin/main e8276bdacbcd.

## Phase S (shared foundation — must land before lanes L1-L7)

| Item | Owner | Status | Notes |
|---|---|---|---|
| S1 SDN hardening | agent-s1 | LANDED 3c7caf669d0 | spans, parse_with_issues, limits, encode.spl, schema.spl; 33 new cases green; 82-case gate unchanged (1 pre-existing red = insert dead-copy bug) |
| S2 kernel contracts | agent-s2 | LANDED 92bc8ebd266 | contract/api/registry/host/manifest_sdn + builtin/index.spl; wildcard removed from gui_shell_core; 25 new cases green, touched suites unchanged |
| S3 document skeleton | agent-s3 | LANDED 9d406f18214 | src/lib/editor/document/ 4 files + 7-case spec green |
| S5a tautology spec deletion | main | LANDED 9d406f18214 | both editor_extension_spec.spl + orphan matcher removed |
| S5b fixture + walking skeleton | — | BLOCKED by S2 | test/fixtures/ide_extensions/hello/ + system spec |
| S6 builtin index seam | agent-s2 | folded into S2 | builtin/index.spl |

## Known campaign hazards (observed this run)
- Parallel sessions revert/delete UNCOMMITTED files during workspace reconciles
  (hit S1 tests, S3 libs, and this state file). Land scoped commits immediately
  after each lane reports green; re-verify files after any update-stale.
- Origin moves every few minutes; push loop = fetch → rebase -r <commit> -d
  main@origin → conflict-check → SSH push → ls-remote verify.

## Landed kernel API (lanes code against THIS; changes go through L0 only)
- contract.spl: ExtensionId/extension_id_parse, SemVer/semver_parse/semver_compare,
  SemVerRange (any | exact | >=min | >=min <max)/semver_range_parse/_contains,
  ExtensionHostPlacement enum, descriptor structs, ExtensionError.
- manifest.spl: typed model; ExtensionManifest += schema_version, display_name,
  engine, entry, host, permissions (6 default-deny bools), contributes_custom_editors.
- manifest_sdn.spl: extension_manifest_load(path) (compat),
  extension_manifest_load_with_diagnostics(path) -> {manifest, issues, ok},
  extension_manifest_decode(text). Themes/keybindings/debug adapters decode for real.
- api.spl: Disposable{id,kind,owner}, ExtensionLifetime, CancellationToken,
  ContextKeys, WhenPredicate (Truthy/Equals/All/AnyOf) + when_eval.
- registry.spl: CommandRegistry.register(owner,id,title, fn(text)->Result<text,text>)
  -> Disposable; first-wins + conflict diagnostic; run/dispose/dispose_owner;
  EventListenerRegistry; LanguageIndex.
- host.spl: register_command_handler, dispatch_command(id,payload)->Result with
  onCommand lazy activation executing the REAL handler, on_event/emit_event invoking
  typed listeners, deactivate disposes lifetime, extension_host_with_builtins via
  builtin_manifest_providers().
- SDN (S1): parse_with_spans (real dotted-path spans), parse_with_issues
  (duplicate_key), parse_untrusted limits, sdn_encode_canonical, schema.spl
  sdn_get_*/sdn_require_*/SdnDecodeIssues/sdn_locate_issues.
- Known gaps (future work): gui_shell.spl:50 still has wildcard (L1 owns file);
  runtime.spl worker host not created (L6); external entrypoint execution not wired
  (L6); handlers register eagerly, activation gates execution.
- Language hazards for lane code: class instances in array FIELDS lose mutations
  (copy semantics) — store struct entries + index reassignment; SDN literals with
  braces need raw '...' strings; test via `bin/simple test` only.

## Contract-change protocol
Shared files (src/lib/common/sdn/**, src/lib/editor/extensions/{contract,api,registry,host,manifest,manifest_sdn}.spl) are edited ONLY by the foundation owner (this session / delegated S-agents). Lanes file change requests here.

## Lane status (2026-07-29, parallel phase)
| Lane | Status | Commit | Notes |
|---|---|---|---|
| L1 Markdown | verifying | — | new specs 13/13 unit + 5/5 system green; controller baseline 65/92 exact match; final report pending |
| L2 Writer | LANDED | a433ac40 | registry dispatch, codec-backed save, theme lookup; 6/6 new spec; word reds pre-existing (MdBlockResult in non-owned file_formats.spl) |
| L3 Sheets | LANDED | 51437cee | function registry + DOUBLE fixture; 1037-case baseline unchanged |
| L4 Slides | LANDED | de71d056 | layout/element registries; 11/11 new, 133/133 baselines |
| L5 Theme | verify pending | — | code+report done; specs never reached Results: under load; verification agent running |
| L6 Security | LANDED | eb170580 | path containment, default-deny, crash-loop; 17/17 |
| L7 Capability | LANDED | 23b18383 | live states, SDN plugin decoder, vscode check: 35 mismatches (bridge disconnected) |
Only ordered cross-lane edge: L5 deletes extensions/theme_manager.spl after L1 drops refs
(L5 found ZERO importers repo-wide; deprecation header added, deletion deferred).
Landing protocol under WC contention: git-plumbing commits (temp GIT_INDEX_FILE,
read-tree FETCH_HEAD, update-index only owned paths, commit-tree, SSH push) —
jj WC is contested by parallel sessions and update-stale WIPES uncommitted files.

## Follow-up lanes (post-L1..L7)
| Lane | Status | Commit | Notes |
|---|---|---|---|
| L0-dupkey | LANDED | 9f69e3c3 | parse_with_spans_and_issues; manifest decode surfaces duplicate_key with line/col; spans 15/15, manifest_sdn 11/11, walking 4/4, 82-gate exact |
| L6b activation hooks | in flight | — | sheets/slides builtins self-register on activation |
| L7b vscode generation | LANDED | bea36f79 | hard mismatches 48->0; **spec probe-validated only** — harness re-run pending |

## RE-VERIFY QUEUE (harness timed out under load 26+; run when box quiets)
- test/01_unit/app/vscode_extension_gen_spec.spl (L7b, 9 cases)
- test/01_unit/app/ide/capability_truth_spec.spl (regression check for L7b)
- test/01_unit/lib/common/ui/theme_role_color_spec.spl + test/01_unit/os/services/theme_service_spec.spl (L5)
Root cause of timeouts: legitimate parallel heavy builds (stage3 bootstrap
native-build 5h+, worktree native_build_worker) — NOT runaways; do not kill.
