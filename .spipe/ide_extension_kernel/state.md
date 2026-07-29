# IDE Extension Kernel Campaign — Coordination State

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

## Lane ownership (plan §3) — starts after Phase S exit gate
L1 Markdown (controller/shell owner) | L2 Writer | L3 Sheets | L4 Slides |
L5 Theme lib-side | L6 isolation/security | L7 capability truth + bridges.
Only ordered cross-lane edge: L5 deletes extensions/theme_manager.spl after L1 drops refs.
