# SStack State: spm-winfs-llm-suite

## User Request
> lets add next feature to simple os, however, make these feature available on windows manager or let windows manager can use them on other os platform. may some needs os support and may some not. if os support needed it can be only impl in simple os......os config env value by privileage.local privileage. id.xxx like privileage. user can devide its privileage more detail and make a group.windows on file system mapping for easy reference gui windows from llm.llm service (like banking) with human approval. or llm.mcp llm wiki/keyword service. (secure contents llm producing check). autority leveling of contents.app to llm approval and communication.llm output filtering and notify user (like pw include or some other information include)

## Plan Reference
> /home/ormastes/.claude/plans/lets-add-next-feature-cozy-kettle.md (user-approved 2026-04-18)

## Task Type
feature

## Refined Goal
> Land the 6-capability SimpleOS + Window Manager suite — hierarchical privilege IDs, windows-on-filesystem (kernel VFS + host parity), LLM→GUI approval via a new **Simple Process Manager (SPM)** service, MCP wiki/keyword tool, content-authority check, and LLM output filter — built on a shared `AuthorityToken` primitive with single-source-of-truth modules under `src/lib/common/{privilege,win_fs,llm,spm}` so SimpleOS and host paths share the same logic.

## Acceptance Criteria
- [ ] AC-1 (Privilege): `src/lib/common/privilege/{id_path,store,group,principal}.spl` modules land. `IdPath` supports intern, prefix match, and subdivide; `PrivilegeStore` persists to `~/.simple/privileges.sdn`; groups expand at check time; all covered by passing specs in `test/lib/common/privilege/`.
- [ ] AC-2 (Win-FS schema): `src/lib/common/win_fs/{window_record,fs_encoder,acl}.spl` encode a `WindowRecord` into a path tree (title/state/geometry/buffer/meta/actions) with round-trip spec green; `acl.spl` consults `PrivilegeStore` and denies open() when id_path does not match.
- [ ] AC-3 (SPM service): `src/app/simple_process_manager/` ships with `spm_service`, `privilege_service`, `window_registry`, `approval_broker`, `llm_gate_service`, and transport trait + SimpleOS-syscall + host-socket impls. End-to-end RPC spec passes with identical payloads on both transports.
- [ ] AC-4 (Win-FS dual mount, no duplication): SimpleOS `src/os/kernel/fs/win_vfs/{win_vfs_mount,win_vfs_driver}.spl` registers `/win` and delegates every operation to shared `fs_encoder` + `win_fs/acl`; host shim `src/app/simple_process_manager/winfs_shim_host.spl` publishes same tree under runtime dir via the same encoder. Grep check in `src/os/kernel/fs/win_vfs/` finds only `import`/`use` of encoder (no inlined encoding). Kernel spec covers mount, readdir, read title, destroy→ENOENT, ACL-denied→EACCES.
- [ ] AC-5 (LLM output filter + notify): `src/app/llm_dashboard/main.spl` and `src/lib/nogc_sync_mut/mcp/` dispatcher route every emit through `src/lib/common/llm/{output_gate,content_authority,notify}.spl` (reusing existing `secret_scan`, `prompt_sanitizer`, `audit_log`). Secret-hit test emits `Hold` + notify routed via SPM + audit row; passwords/keys/PII detected and gated.
- [ ] AC-6 (Approval + MCP wiki): `src/app/mcp/wiki_keyword/{wiki_tool,register}.spl` exposes MCP tool returning content tagged with `ContentAuthority`; lower-clearance consumer gets `Hold`. Approval broker spec: SimpleOS z-band reserved surface only SPM can composite into; host dialog accepts only SPM-signed actions (per-boot chrome secret). Spoofed actions rejected in spec.
- [ ] AC-7 (Verification + docs): `bin/simple test` green on new specs; no regressions; `bin/simple build check` passes; architecture docs added/updated: `doc/04_architecture/{simple_process_manager,privilege_id_system,win_fs_schema}.md` and `doc/07_guide/tooling/llm_approval_flow.md`; `mdsoc_architecture_tobe.md` references SPM service layer.

## Cooperative Providers
- Codex: available (`~/.npm-global/bin/codex`)
- Gemini: available (`~/.npm-global/bin/gemini`)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-04-18
- [x] 2-research — 2026-04-18
- [x] 3-arch — 2026-04-18
- [x] 4-spec (QA Lead) — 2026-04-18
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Date:** 2026-04-18
**Task Type:** feature
**Feature slug:** spm-winfs-llm-suite

**Summary.** User request refined into 6-capability feature suite anchored by a new shared service (Simple Process Manager / SPM) and unifying primitive (`AuthorityToken`). Scope, constraints, and module layout are fully specified in the approved plan at `/home/ormastes/.claude/plans/lets-add-next-feature-cozy-kettle.md` — this state file references the plan rather than duplicating it.

**Key decisions locked in Phase 1:**
1. All 6 capabilities land in a single iteration (user confirmed).
2. `Privilege` structure is **orthogonal to existing `CapabilityToken`** — kernel enforces both independently.
3. Win-FS: **real kernel VFS mount on SimpleOS** + same tree mirrored on host via shared `fs_encoder` — no duplicated logic.
4. SWM delegates approval to **SPM** (one service, two transports).
5. All code in `.spl`; MDSOC+ for userland, MDSOC-only for kernel.
6. Existing primitives reused (no redefinition): `secret_scan`, `prompt_sanitizer`, `audit_log`, `credential_store`, `TrustLevel`.

**Ambiguities resolved:**
- Delivery scope → all 6 in one iteration.
- Privilege shape → parallel `Privilege` structure (not `CapabilityToken` field).
- Approval surface → SWM draws, SPM authorizes (shared on both environments).
- Win-FS → real kernel mount on SimpleOS + host parity via shared encoder.

**Deferred (explicit):**
- Cross-machine privilege federation.
- MCP wiki corpus population (ship framework + minimal stub).
- Real FUSE binding on Linux (fall back to runtime-dir reflection if std bindings absent).

### 2-research
**Date:** 2026-04-18
**Agent:** Analyst (Claude); cross-check via Codex.

#### 1. Reusable primitives — confirmed APIs
- `src/app/tools/secret_scan.spl` — `class SecretScanner` (L32), `class SecretMatch` (L17), `class SecretPattern` (L25). Pattern match helpers `match_pattern`/`extract_match` at L150/L198. Formatters `format_results`/`format_results_json` at L544/L561. Scanner is line-oriented — wrap for streaming LLM tokens.
- `src/lib/common/security/validation/prompt_sanitizer.spl` — `class PromptSanitizer` with `sanitize_input`, plus `inject_canary` / `detect_canary` free fns (canary model → useful for LLM output filter detecting prompt-leak echoes). Delimiter wrapping, blocked pattern filter, length limit.
- `src/lib/common/security/audit_log.spl` — single-entry point `fn log_security_event(entry: AuditEntry, config: AuditConfig)` (L12). Helpers: `format_audit_entry` (L28), `event_type_name` (L36), `event_to_fields` (L57), `mask_value` (L84), `severity_name` (L98), `meets_severity` (L105). Header comment marks it as "AOP weaving target — business code does NOT call these functions directly". Phase 3 must decide: call through weaving or direct.
- `src/lib/common/security/auth/credential_store.spl` — opaque `CredentialHandle`, `CredentialStore` with `apply()` callback pattern (never returns raw value). Read path `~/.simple/credentials.sdn`; this is the precedent for our `~/.simple/privileges.sdn`.
- `src/app/package.registry/trust.spl` — `enum TrustLevel { RegistryTrusted, UserTrusted, Untrusted, Revoked }`; `class TrustStore` loaded from `~/.simple/trusted_signers.sdn` with `TrustStore.default()` (L~57 in snippet). Reuse enum as `TrustSource` alias — do NOT redefine.
- `src/os/kernel/types/capability_types.spl` — `struct CapabilityToken { kind: CapabilityKind, generation: u64, owner: u64 }`; `enum CapabilityKind` includes `SystemPrivilege` already (gate for `sys_privctl`); `struct CapabilitySet { caps: [CapabilityToken], is_pledged: bool }` with `full()`, `has(kind)`, `pledge(allowed)`. G11 `PrivilegeMask` (bitmap) and `sys_privctl` opcodes exist — our new hierarchical `Privilege` must not collide with this bitmap namespace.
- MCP dispatcher: only `handle_tool_call` found is in `src/lib/nogc_sync_mut/mcp/jj/main.spl:147` (call site) and L222 (def): `fn handle_tool_call(id: String, tool_name: String, body: String, repo_path: String) -> String`. Other MCP handlers (e.g. `mcp/handlers/debug_handler.spl`) use a per-file `main()` that switches on `args[1]` tool name (no shared dispatcher). **Finding: there is no single central dispatcher.** Phase 3 must pick: (a) wrap each handler's entry, (b) introduce a shared `mcp/dispatch.spl` and retrofit, or (c) add the gate inside each tool file. Preferred: (b).

#### 2. Existing SPM-like code — name-collision scan
- No existing `process_manager` / `service_manager` / `session_daemon` / `spm_*` directory or file under `src/` (searched `src/app/**` and `src/os/**`).
- `src/app/` subdirs that share namespace semantics: `audit/`, `dashboard/`, `container/`, `desugar/`, `io/` — no collision with `simple_process_manager/`.
- Safe to land new paths: `src/app/simple_process_manager/`, `src/lib/common/spm/`, `src/os/kernel/fs/win_vfs/`.

#### 3. Kernel VFS driver pattern — actual location differs from plan
- **Trait lives at `src/os/services/vfs/vfs.spl`**, not `src/os/kernel/fs/`. The only file under `src/os/kernel/fs/` is `fat32.spl` (a standalone driver).
- `trait Filesystem`:
  `fn fs_name() -> text` / `fn mount(device: text, options: text) -> Result<bool, text>` / `fn unmount() -> Result<bool, text>` / `fn open(path: text, flags: FileFlags) -> Result<u64, text>` / `fn read(handle: u64, size: u64) -> Result<[u8], text>` / `fn write(handle: u64, data: [u8]) -> Result<u64, text>` / `fn close(handle: u64) -> Result<bool, text>` / `fn seek(handle: u64, offset: i64, whence: SeekWhence) -> Result<u64, text>` / `fn stat(path: text) -> Result<FsNode, text>` / `fn chmod(path: text, mode: u16) -> Result<bool, text>` / `fn mkdir(path: text) -> Result<bool, text>` / `fn rmdir(path: text) -> Result<bool, text>` / `fn readdir(path: text) -> Result<[DirEntry], text>` / `fn unlink(path: text) -> Result<bool, text>` / `fn rename` / `fn symlink`.
- Registration via `class VfsManager { mounts: [MountEntry], next_fd }` with `me mount(path: text, fs_type: text, device: text, read_only: bool, fs: Filesystem)`.
- **Plan correction for Phase 3:** win_vfs driver must implement `trait Filesystem` (not a hypothetical `VfsDriver`) and register with `VfsManager` under service path — the plan's path `src/os/kernel/fs/win_vfs/` works as a code location but the trait is imported from `os.services.vfs.vfs`.

#### 4. WM ↔ kernel IPC & syscall_raw surface
- `src/os/compositor/wm_core.spl` is **pure logic** (hit-test, z-order, resize) — "No compositor state, no FFI — all functions are deterministic and testable". IPC does NOT flow through it today. Phase 3 must add IPC calls through a **new** sibling module (`wm_spm_client.spl`) or inside `hosted_backend*.spl` / a new `bare_metal_backend.spl`, not `wm_core.spl`.
- `src/os/userlib/syscall_raw.spl` is a **stub**: only three per-arch overloads of `fn syscall(id: u64, arg0..arg4: u64) -> i64` (lines 10/32/54). No `sys_ipc`, `sys_priv_check`, `sys_win_register`, `sys_approval_request` exist yet. Phase 3 must add these wrappers and matching `SYS_*` constants in `src/os/kernel/types/syscall_types.spl`.
- Hosted backend chain: `src/os/compositor/hosted_backend.spl` → `hosted_backend_cocoa.spl` / `hosted_backend_win32.spl`, dispatched by `select_hosted_backend()` using env `SIMPLE_HOSTED_SURFACE` + host triple from `rt_hosted_select_surface`. This is the right layer to plug `wm_spm_client` into for host-mode RPC.
- Kernel IPC files: `src/os/kernel/ipc/{ipc,ports,message_buffer,notif_global,notification,syscall,capability}.spl`. `capability.spl` has `class CapabilityManager` (L40) with `check_file_access(task, path, perm)` (L76), inner `check(from, kind)` used at L108, `revoke_all_for_task` (L205). This is where Phase 3 adds the "two-gate" hook (existing `CapabilitySet.has()` AND new `privilege_service` call).

#### 5. Portable SDN storage pattern
- **SDN parse/encode helpers:** `src/lib/common/ui/parse/sdn.spl` (flat-entry parser: `parse_to_flat(source) -> [FlatEntry]` L115, `flat_get` L166, `flat_child_keys` L172) and `src/lib/common/ui/parse/sdn_tree.spl` (tree form: `build_tree_from_source` L212, `build_widget_node` L229). Naming is UI-biased but the parser is domain-neutral.
- **SDN value model** (nogc_sync_mut): `parse_sdn(content: text) -> Result<SdnValue, text>` at `src/lib/nogc_sync_mut/src/exp/config.spl:428` and `src/lib/nogc_sync_mut/src/config.spl:618`. `sdn_value_to_text` at `src/lib/nogc_sync_mut/db_atomic.spl:488` gives the canonical encoder.
- **Write-to-disk precedent:** `trust.spl` uses `std.fs.{read_file, write_file}` plus an in-module `serialize_trust_store(store) -> text` (custom SDN emission). `credential_store.spl` reads `~/.simple/credentials.sdn` via its own `_read_credential_from_file`. Pattern: each module owns its serializer + reuses the common flat/tree parser.
- **`~/.simple` home:** `trust.spl` computes `val home = home_dir(); val path = "{home}/.simple/trusted_signers.sdn"`. Phase 3 `PrivilegeStore` should mirror this idiom for `~/.simple/privileges.sdn`.

#### 6. LLM dashboard emit choke point
- `src/app/llm_dashboard/main.spl` (135 lines) is a thin launcher: `run_gui_dashboard` constructs `DashboardServer.new_with_agent_dir(port, watch_dir)` and calls `server.start()`; `run_tui_dashboard_subprocess` shells out to `src/app/llm_dashboard/tui_main.spl`. **No emits happen here** — the plan's "every LLM emit passes through `output_gate`" must hook deeper.
- **HTTP response choke point:** `src/app/web_dashboard/server.spl` — `fn http_response(status, content_type, body) -> text` (L456), `fn http_response_with_headers` (L459). All HTTP responses build through L456. Every `class DashboardServer` route returns `http_response(...)` (see L190/197/213/221/272/278/305/328/352/377/393/411/425/448). `me start()` eventually calls `stream.write_text(response)` at L154 — that is the TCP sink.
- **WebSocket / streaming path:** `src/app/llm_dashboard/gui/ws_handler.spl` plus per-panel HTML in `gui/*_html.spl`. LLM tokens reach the browser via `ws_handler` and panel HTML builders (e.g. `message_panel_html.spl`, `mcp_panel_html.spl`, `terminal_panel.spl`).
- **TUI path:** `src/app/llm_dashboard/tui_main.spl` + `tui/activity_feed.spl`.
- **Filter placement recommendation (for Phase 3):** single-choke point does not exist naturally; insert `llm_gate_service` at **two** narrow seams — (a) `http_response` / `http_response_with_headers` body-filter hook in `src/app/web_dashboard/server.spl` (filter body before write), and (b) `ws_handler.spl` outbound message hook. Also hook MCP tool results at the tool-dispatch retrofit point (Phase 3 §1 shared `mcp/dispatch.spl`).
- `web_login.spl` currently declares `capabilities: [text]` on both `DashboardAuthUser` (L26) and `DashboardAuthSession` (L34); `_default_admin_capabilities()` at L327 returns text list; SDN persists via `content.push("capabilities={user.capabilities.join(",")}")` at L219/L247. Migration per AC-5 is a direct re-key in that writer.

#### 7. Cross-check (Codex)
Codex (gpt-5.4) reachable, returned bulleted cross-check:
- **Token namespace drift / group explosion** — Android + macOS TCC show hierarchical permission trees grow unreviewable. Mitigation: small stable taxonomy, version it, broker-side lint for new families before they ship.
- **Confused deputy between capability tokens and privilege tokens** — Capsicum is safe because object-caps resist ambient authority; orthogonal trees can reintroduce "hold FD but lack privilege" (or inverse). Mitigation: SPM mint bundles both FD/object identity and privilege set atomically with explicit delegation rules + audit.
- **Approval-surface spoofing & user fatigue** — polkit/Android/TCC prove users train to click through, fake attributions get exploited. Mitigation: WM-owned unforgeable chrome tied to focused-window/process lineage; stable app identity + exact requested action in dialog; rate-limit/replay-protect.
- **Prompt-path deadlock / liveness** — SPM as sole approval surface + synchronous scan+notify cycle can freeze launches. Mitigation: watchdog + timeout; crash-only restart; kernel/WM emergency path independent of SPM; Plan 9 9P inspired async publish/subscribe so `/win` readers never block on SPM.
- **/win staleness & revocation gaps** — Plan 9 live VFS is great but consumers cache; TCC revocation often lags running processes. Mitigation: generation counter on `WindowRecord` (reuse `CapabilityToken.generation` pattern), kernel-side ENOENT on stale `wid`, SPM push-revoke via notify port.

#### 8. Risks (merged Claude + Codex)
1. **Confused-deputy between `CapabilitySet` and `AuthorityToken`.** Two gates that disagree create bypasses. Mitigation: `CapabilityManager.check()` and `privilege_service.check()` called from one kernel hook in `src/os/kernel/ipc/capability.spl`; both-must-pass is the only composition rule; unit spec covers "cap-only", "priv-only", "both", "neither".
2. **MCP has no central dispatcher** — retrofitting to every per-tool `main()` is noisy. Mitigation: Phase 3 introduces `src/lib/nogc_sync_mut/mcp/dispatch.spl` with `fn handle_tool_call(session, tool_name, body) -> text` wrapping pre-check (`privilege_service`) + post-check (`llm_gate_service`), and migrate existing handlers (jj + debug) to it in one commit; non-migrated handlers fail closed.
3. **Approval-surface deadlock.** SPM blocks on kernel blocks on SWM blocks on SPM. Mitigation: approval is **async pending-request** model — SPM writes `pending_request.sdn` under approval namespace; SWM polls via `readdir`/notification port; user decision posted back as separate RPC. Kernel never blocks on SWM.
4. **`~/.simple/privileges.sdn` write race + corruption.** Two processes (SPM + dashboard migrator) writing concurrently. Mitigation: follow `credential_store`/`trust.spl` pattern — SPM owns the only writer; other readers go through SPM RPC. Phase 3 adds temp-file + atomic rename in `PrivilegeStore.save()`.
5. **llm_dashboard has no single emit point.** Three sinks (HTTP, WS, TUI). Mitigation: wrap each sink with `llm_gate_service.scan_and_gate(text, token)`; gate returns original text (pass), redacted text (Scrub), or `Hold` marker; all three sinks share one gate call so adding a sink later is a compile-time failure (trait-bound).
6. **`wm_core.spl` is pure** — cannot be modified to call IPC without breaking its test contract. Mitigation: plan has correct approach — add new `wm_spm_client.spl` and call it from `hosted_backend.spl` / future baremetal backend; update plan to explicitly not touch `wm_core.spl`.
<!-- exit-criteria: section under 200 lines; 8 numbered subsections + risks + cross-check -->

### 3-arch
**Date:** 2026-04-18  **Agent:** Architect (Claude); cross-check Codex + Gemini.

#### A. Module list (new / modified)
| Path | Role | N/M |
|------|------|-----|
| `src/lib/common/privilege/id_path.spl` | `IdPath` + intern table, prefix match, subdivide | New |
| `src/lib/common/privilege/principal.spl` | `Principal{kind:PrincipalKind, id:text}` | New |
| `src/lib/common/privilege/authority_token.spl` | `AuthorityToken`, `AuthorityLevel`, `Scope` | New |
| `src/lib/common/privilege/group.spl` | Group expansion (pure) | New |
| `src/lib/common/privilege/store.spl` | **pure** SDN encode/decode of `PrivilegeStore` (no fs I/O) | New |
| `src/lib/nogc_sync_mut/privilege/store_fs.spl` | `load_sdn`/`save_sdn` (atomic rename) for `~/.simple/privileges.sdn` | New |
| `src/lib/common/win_fs/window_record.spl` | `WindowRecord`, `Rect`, `BufferRef`, `WindowState`, `FsOp` | New |
| `src/lib/common/win_fs/fs_encoder.spl` | `trait FsEncoder`, default impl (path-tree ↔ record) | New |
| `src/lib/common/win_fs/acl.spl` | `acl_check(rec, token, op)` — pure policy | New |
| `src/lib/common/llm/content_authority.spl` | `ContentAuthority`, `release_gate`, `TrustLevel` re-export | New |
| `src/lib/common/llm/output_gate.spl` | pure `scan_and_gate` + `filter_response_body` (no notify I/O) | New |
| `src/lib/nogc_sync_mut/llm/notify.spl` | notify adapter (writes via SPM RPC; I/O layer) | New |
| `src/lib/nogc_sync_mut/mcp/dispatch.spl` | `DispatchRegistry` + `dispatch_wrap` (explicit registration) | New |
| `src/app/simple_process_manager/spm_service.spl` | daemon entry; owns transports | New |
| `src/app/simple_process_manager/privilege_service.spl` | check/mint/revoke RPC surface | New |
| `src/app/simple_process_manager/window_registry.spl` | in-memory `[WindowRecord]` + generation counter | New |
| `src/app/simple_process_manager/approval_broker.spl` | async pending-request pattern | New |
| `src/app/simple_process_manager/llm_gate_service.spl` | wraps `output_gate` + `notify` | New |
| `src/app/simple_process_manager/winfs_shim_host.spl` | host reflection of `/win` via `fs_encoder` | New |
| `src/app/simple_process_manager/wm_spm_client.spl` | RPC client; called from compositor backends | New |
| `src/app/simple_process_manager/transport.spl` | `trait SpmTransport`, SPM request/response types | New |
| `src/app/simple_process_manager/transport_simpleos.spl` | syscall-backed `SpmTransport` impl | New |
| `src/app/simple_process_manager/transport_host.spl` | unix-socket `SpmTransport` impl | New |
| `src/os/kernel/fs/win_vfs/win_vfs_driver.spl` | `impl Filesystem for WinVfsDriver` | New |
| `src/os/kernel/fs/win_vfs/win_vfs_mount.spl` | registers `/win` with `VfsManager` | New |
| `src/os/kernel/privilege/privilege_bridge.spl` | kernel-side `IdPath` mirror (plain bitmap+bytes); NEVER imports userland privilege module | New |
| `src/app/mcp/wiki_keyword/{wiki_tool,register}.spl` | MCP wiki tool via `dispatch_wrap` | New |
| `src/os/kernel/ipc/capability.spl` | add `privilege_bridge.check()` sibling call at `check_file_access` | Modified |
| `src/os/compositor/hosted_backend.spl` | call `wm_spm_client` on window lifecycle | Modified |
| `src/os/compositor/baremetal_backend.spl` | same — syscall transport path | Modified (new-if-absent) |
| `src/os/userlib/syscall_raw.spl` | add `sys_priv_check`/`sys_win_register`/`sys_approval_request` wrappers | Modified |
| `src/os/kernel/types/syscall_types.spl` | add `SYS_PRIV_CHECK`/`SYS_WIN_REGISTER`/`SYS_APPROVAL_REQUEST` | Modified |
| `src/app/web_dashboard/server.spl` | `http_response` L456/459 call `output_gate.filter_response_body` | Modified |
| `src/app/llm_dashboard/gui/ws_handler.spl` | wrap outbound frame through gate | Modified |
| `src/app/llm_dashboard/tui/activity_feed.spl` | wrap emit through gate | Modified |
| `src/lib/nogc_sync_mut/mcp/jj/main.spl` | migrate to `dispatch_wrap` (pilot) | Modified |
| `src/lib/nogc_sync_mut/mcp/handlers/debug_handler.spl` | migrate to `dispatch_wrap` (pilot) | Modified |
| `test/lib/common/privilege/*_spec.spl` (4 files) | IdPath / store / group / authority_token specs | New |
| `test/lib/common/win_fs/{encoder,acl}_spec.spl` | encoder round-trip + ACL | New |
| `test/lib/common/llm/{output_gate,content_authority}_spec.spl` | gate + release | New |
| `test/app/simple_process_manager/{spm_rpc,approval,window_registry}_spec.spl` | RPC parity both transports | New |
| `test/os/kernel/fs/win_vfs/win_vfs_spec.spl` | mount/readdir/destroy/EACCES | New |
| `test/app/mcp/wiki_keyword_spec.spl` | authority-tagged content gate | New |

MDSOC check: kernel files (`src/os/**`) import only `os.services.vfs.vfs`, kernel-local `privilege_bridge`, and existing kernel types — no `src/lib/common/privilege` reach-in. Userland (`src/app/**`, `src/lib/**`) is MDSOC+ (composition + ECS components in SPM window_registry).

#### B. Key interfaces (Simple syntax)
```spl
# src/lib/common/privilege/id_path.spl
class IdPath { segments: [text], intern_id: u32 }   # intern_id is a dedupe handle, NOT a capability FD
fn id_path_intern(s: text) -> IdPath
fn id_path_prefix_match(granted: IdPath, required: IdPath) -> bool
fn id_path_subdivide(parent: IdPath, child: text) -> Result<IdPath, Error>

# src/lib/common/privilege/authority_token.spl
enum AuthorityLevel { Public, Internal, Sensitive, Secret }
enum TrustSource { RegistryTrusted, UserTrusted, Untrusted, Revoked }   # alias of pkg trust
class Scope { ttl_ms: u64, once: bool, bound_wid: u64 }
class AuthorityToken {
    id_path: IdPath, authority: AuthorityLevel, principal: Principal,
    trust_source: TrustSource, scope: Scope, issuer_sig: [u8]
}

# src/lib/common/privilege/store.spl  (pure; I/O split out)
class PrivilegeStore { tokens: [AuthorityToken], groups: [GroupDecl] }
me PrivilegeStore.lookup(principal: Principal, id_path: IdPath) -> Option<AuthorityToken>
me PrivilegeStore.mint(parent: AuthorityToken, child: IdPath, level: AuthorityLevel) -> Result<AuthorityToken, Error>
me PrivilegeStore.revoke(token_sig: [u8]) -> ()
me PrivilegeStore.expand_groups(id_path: IdPath) -> [IdPath]
fn privilege_store_decode(source: text) -> Result<PrivilegeStore, Error>
fn privilege_store_encode(store: PrivilegeStore) -> text
# src/lib/nogc_sync_mut/privilege/store_fs.spl
fn load_sdn(path: text) -> Result<PrivilegeStore, Error>
fn save_sdn(store: PrivilegeStore, path: text) -> Result<(), Error>   # temp-file + atomic rename

# src/lib/common/win_fs/window_record.spl
enum WindowState { Hidden, Normal, Minimized, Maximized, Destroyed }
class Rect { x: i32, y: i32, w: u32, h: u32 }
class BufferRef { kind: text, handle: u64, bytes: u64 }
enum FsOp { Open, Read, Write, Readdir, Stat, Unlink }
class WindowRecord {
    wid: u64, generation: u32, app: text, title: text,
    state: WindowState, geometry: Rect, buffer_ref: BufferRef, acl_id_path: IdPath
}

# src/lib/common/win_fs/fs_encoder.spl
class FsTree { entries: [FsEntry] }
trait FsEncoder {
    fn encode_record(rec: WindowRecord) -> FsTree
    fn decode_tree(tree: FsTree) -> Result<WindowRecord, Error>
    fn acl_check(rec: WindowRecord, token: AuthorityToken, op: FsOp) -> bool
}

# src/app/simple_process_manager/transport.spl
class SpmRequest  { kind: text, body: [u8], token_hint: Option<AuthorityToken> }
class SpmResponse { ok: bool, body: [u8], error: Option<Error> }
trait SpmTransport {
    fn send(req: SpmRequest) -> Result<SpmResponse, Error>
    fn listen(handler: Fn<SpmRequest, SpmResponse>) -> ()
}
class SpmTransportSimpleos { }    # syscall-backed
class SpmTransportHost     { sock_path: text }

# src/app/simple_process_manager/approval_broker.spl
class ApprovalIntent { app: text, action: text, required: IdPath, level: AuthorityLevel }
class SignedAction   { intent: ApprovalIntent, principal: Principal, hmac: [u8] }
class ApprovalBroker { pending_dir: text, chrome_secret: [u8] }
me ApprovalBroker.request_approval(intent: ApprovalIntent, principal: Principal) -> Result<AuthorityToken, Error>
me ApprovalBroker.verify_response(signed: SignedAction) -> bool

# src/lib/common/llm/output_gate.spl (pure)
enum GateDecision { Pass, Hold(reasons: [text]), Deny }
class OutputGate { scanner: SecretScanner, sanitizer: PromptSanitizer }
me OutputGate.scan_and_gate(body: [u8], token: AuthorityToken) -> GateDecision
me OutputGate.filter_response_body(body: [u8], token: AuthorityToken) -> [u8]   # Pass=passthrough, Hold=redacted bytes, Deny=empty+flag

# src/lib/common/llm/content_authority.spl
enum ReleaseDecision { Release, Scrub(reasons: [text]), Block }
class ContentAuthority { level: AuthorityLevel, source_trust: TrustSource }
fn release_gate(content: ContentAuthority, reader_clearance: AuthorityLevel) -> ReleaseDecision

# src/os/kernel/fs/win_vfs/win_vfs_driver.spl (implements existing trait)
class WinVfsDriver { encoder: FsEncoder, registry_ref: WindowRegistryRef }
impl Filesystem for WinVfsDriver {
    fn fs_name() -> text                                       # "win"
    fn mount(device: text, options: text) -> Result<bool, text>
    fn readdir(path: text) -> Result<[DirEntry], text>
    fn open(path: text, flags: FileFlags) -> Result<u64, text>
    fn read(handle: u64, size: u64) -> Result<[u8], text>
    # (write/close/stat/unmount also implemented; stat/close trivial)
}

# src/lib/nogc_sync_mut/mcp/dispatch.spl  (~15-line wrapper)
class DispatchEntry { tool_name: text, required: IdPath, level: AuthorityLevel, handler: Fn<[text], Result<[u8], Error>> }
class DispatchRegistry { entries: [DispatchEntry] }
me DispatchRegistry.register(e: DispatchEntry) -> ()
fn dispatch_wrap(reg: DispatchRegistry, tool_name: text, args: [text], token_hint: Option<AuthorityToken>) -> text {
    if entry = reg.find(tool_name) {                           # explicit registration gate
        if !privilege_service_check(entry.required, entry.level, token_hint) {
            return mcp_error_json("EACCES")
        }
        if result = entry.handler(args) {
            val token = token_hint.unwrap_or(AuthorityToken.public())
            val gated = OutputGate.default().filter_response_body(result, token)
            return mcp_ok_json(gated)
        } else { return mcp_error_json(result.error_text()) }
    }
    return mcp_error_json("unregistered_tool")                 # fail-closed for registered callers
}
```

#### C. Data flows (end-to-end)
**Banking LLM asks to open window:** LLM tool-call → `mcp/dispatch.wrap` (privilege_service.check denies without Banking.* token) → `approval_broker.request_approval` writes `pending_request.sdn` → SWM lists via `/win/pending` → user clicks signed Yes on SPM-chrome → `verify_response` HMAC-ok → mint `AuthorityToken` (Sensitive, bound_wid) → `window_registry.create` → `wm_spm_client.open(wid)` → composited.

**LLM emits secret:** Token stream reaches `web_dashboard/server.http_response` → `output_gate.filter_response_body(body, token)` → `scan_and_gate` hits `secret_scan` + `prompt_sanitizer.detect_canary` → `Hold(reasons)` → body replaced with redacted bytes + `llm_gate_service.notify()` → SPM RPC → audit row via `log_security_event` → user toast. Same path for WS + TUI.

**Host-run SWM opening a window:** host compositor `hosted_backend.create_window()` → `wm_spm_client.register(WindowRecord)` → `transport_host` unix-socket → `spm_service` → `window_registry.insert` (generation++) → `winfs_shim_host` writes FsTree under `$XDG_RUNTIME_DIR/simple/win/` via same `FsEncoder` → LLM tool reads via stdlib fs (no kernel VFS needed).

#### D. Integration points (existing-file modifications)
- `src/os/kernel/ipc/capability.spl` — after `CapabilityManager.check()` (~L108) add sibling `privilege_bridge.check(task, id_path, level)`; both-must-pass. Kernel imports only `os.kernel.privilege.privilege_bridge` (kernel-local); `privilege_bridge` receives pre-parsed plain bytes/bitmap set by SPM via syscall — **no kernel ↔ `src/lib/common` dependency**.
- `src/os/userlib/syscall_raw.spl` — add `fn sys_priv_check(id_path_ptr, level) -> i64`, `fn sys_win_register(record_ptr) -> i64`, `fn sys_approval_request(intent_ptr) -> i64`; extend existing 3 overload stubs.
- `src/os/kernel/types/syscall_types.spl` — add `const SYS_PRIV_CHECK`, `SYS_WIN_REGISTER`, `SYS_APPROVAL_REQUEST` at next free ids.
- `src/os/compositor/hosted_backend.spl` — on window create/destroy/resize call `wm_spm_client.notify(...)`. Do NOT touch `wm_core.spl`.
- `src/os/compositor/baremetal_backend.spl` — same surface, uses `transport_simpleos`.
- `src/app/web_dashboard/server.spl` — `http_response` L456 and `http_response_with_headers` L459: filter `body` through `OutputGate.filter_response_body(body, session_token)` before `stream.write_text(response)` at L154.
- `src/app/llm_dashboard/gui/ws_handler.spl` — wrap outbound frame payload through the same gate.
- `src/app/llm_dashboard/tui/activity_feed.spl` — wrap line emit through the same gate.
- `src/lib/nogc_sync_mut/mcp/jj/main.spl` (`handle_tool_call` L222) — migrate to `DispatchRegistry.register(...)` + `dispatch_wrap` (pilot).
- `src/lib/nogc_sync_mut/mcp/handlers/debug_handler.spl` — same migration (pilot).

#### E. Naming coexistence
- New types live under `src/lib/common/privilege/` namespace: `IdPath`, `AuthorityToken`, `AuthorityLevel`, `PrivilegeStore`, `Principal`, `TrustSource`, `Scope`, `GroupDecl`.
- Existing kernel `PrivilegeMask` (bitmap) + `sys_privctl` in `src/os/kernel/types/capability_types.spl` remain **unchanged** and **kernel-local**; no rename.
- Kernel never imports `src/lib/common/privilege/*`. `src/os/kernel/privilege/privilege_bridge.spl` is a kernel-local mirror — receives plain bytes from SPM via syscall payload, exposes `check(task, id_path_bytes, level) -> bool`; no shared types cross the MDSOC boundary. Addresses Codex "MDSOC violation" finding.

#### F. MCP dispatcher wrap boundary (opt-in → explicit registration)
- Shape: each migrating tool's `main()` calls `DispatchRegistry.default().register(DispatchEntry{ "tool.name", required_id_path, level, fn(args) -> Result<[u8],Error> { ... } })`, then routes incoming stdin through `dispatch_wrap(reg, tool, args, token_hint)`.
- **Fail-closed for registered callers** (unregistered tool name on a registry-using server → `EACCES`). Legacy handlers that have NOT migrated keep their existing `main()` and remain functional (fail-open at process scope, but the SPM broker won't route privileged intents to them — they lose the privileged-tool ambient).
- Migration is tracked in a static `dispatch_audit.sdn` checked into repo; Phase 5 migrates jj + debug handlers as pilot; Phase 6 CI lints that any tool accepting sensitive inputs is present in the audit file (answers Codex "silent bypass" concern).
- The 15-line `dispatch_wrap` body above is the entire hot path: registry lookup → privilege check → handler invoke → output gate → JSON reply. No I/O beyond what the handler itself does.

#### G. Cross-check (Codex + Gemini)
**Codex (gpt-5.4) — accepted & folded in:**
- "Two authority planes risk confused deputy" → resolved via kernel-local `privilege_bridge` mirror; kernel sees only plain bytes; userland `AuthorityToken` never crosses the syscall. SPM is the only minter.
- "MDSOC violation if kernel imports userland AuthorityToken" → resolved by splitting: `src/lib/common/privilege/*` (userland), `src/os/kernel/privilege/privilege_bridge.spl` (kernel-local). Zero cross-import.
- "`dispatch_wrap<T>(...)->text` is signature-fragile" → resolved: handler returns `Result<[u8], Error>`; wrapper returns `text` (JSON); registry carries `(IdPath, AuthorityLevel)` so authority is not hidden in args.
- "Opt-in MCP wrap is fail-open" → resolved via explicit `DispatchRegistry.register(...)` + audit file + Phase 6 lint.

**Gemini — accepted partially:**
- "Chrome secret high-friction; OCR can clone" → accepted. Host fallback ranks: (1) OS-native (TouchID / Windows Hello / polkit agent over unix socket) when available, (2) unix-socket peercred-bound dialog process the compositor launches under SPM parent, (3) chrome-secret-marker only as last resort (documented as weak).
- "Action Sensitivity Levels to reduce fatigue" → adopted: `AuthorityLevel` gates the surface — `Public`/`Internal` auto-approved with audit; `Sensitive` needs per-session allow; `Secret` needs per-action biometric/OOB.
- Approval_broker adds a platform probe: tries polkit/TouchID/Hello first and only falls back to chrome-secret when none present.
<!-- exit-criteria: module list, interface signatures (no inheritance; composition/traits only), data flow, MDSOC respected, cross-check folded in. -->


### 4-spec
**Date:** 2026-04-18  **Agent:** QA Lead (Claude).

**Summary.** 16 failing SSpec `.spl` files land under `test/` mirroring the Phase 3 module layout. All tests are **red** — the modules under `src/lib/common/{privilege,win_fs,llm}`, `src/app/simple_process_manager/`, `src/app/mcp/wiki_keyword/`, `src/lib/nogc_sync_mut/mcp/dispatch.spl`, and `src/os/kernel/fs/win_vfs/` do not yet exist. Tests import the exact type/function names defined in Phase 3 §B. Only built-in SSpec matchers used. Every file carries a `# @cover` marker so coverage tooling tracks the target impl.

**Spec files created (absolute paths).**
- `/home/ormastes/dev/pub/simple/test/lib/common/privilege/id_path_spec.spl` — AC-1: intern dedup, prefix match (pos/neg/sibling), subdivide, segment validation (dot + empty rejected).
- `/home/ormastes/dev/pub/simple/test/lib/common/privilege/store_spec.spl` — AC-1: mint/lookup/revoke round-trip, group expansion, SDN encode/decode + `store_fs` disk round-trip.
- `/home/ormastes/dev/pub/simple/test/lib/common/privilege/group_spec.spl` — AC-1: flat membership + nested (transitive) group expansion.
- `/home/ormastes/dev/pub/simple/test/lib/common/privilege/principal_spec.spl` — AC-1: local-default, validation pass/fail for remote kind.
- `/home/ormastes/dev/pub/simple/test/lib/common/win_fs/fs_encoder_spec.spl` — AC-2: WindowRecord ↔ FsTree round-trip + schema path shape `/<app>/<wid>/{title,state,geometry,buffer,meta,actions}`.
- `/home/ormastes/dev/pub/simple/test/lib/common/win_fs/acl_spec.spl` — AC-2/AC-4: open() allow/deny by prefix; revoked token denied.
- `/home/ormastes/dev/pub/simple/test/lib/common/win_fs/window_record_spec.spl` — AC-2: create / update_title (generation bump) / mark_destroyed.
- `/home/ormastes/dev/pub/simple/test/lib/common/llm/output_gate_spec.spl` — AC-5: clean=Pass; AWS key / phone / email = Hold; `filter_response_body` Hold path redacts bytes + emits notify + audit.
- `/home/ormastes/dev/pub/simple/test/lib/common/llm/content_authority_spec.spl` — AC-6: release_gate Release/Scrub/Block by clearance; Revoked trust → Block.
- `/home/ormastes/dev/pub/simple/test/app/simple_process_manager/spm_service_spec.spl` — AC-3: host + SimpleOS transport parity; priv_check allow/deny; win_register persists.
- `/home/ormastes/dev/pub/simple/test/app/simple_process_manager/approval_broker_spec.spl` — AC-6: request_approval happy-path; verify_response accepts SPM-signed, rejects unsigned + forged.
- `/home/ormastes/dev/pub/simple/test/app/mcp/wiki_keyword/wiki_tool_spec.spl` — AC-6: Content tagged with ContentAuthority; lower-clearance consumer gets Scrub/Block; registration into DispatchRegistry.
- `/home/ormastes/dev/pub/simple/test/lib/nogc_sync_mut/mcp/dispatch_spec.spl` — AC-5/AC-6: registered tool runs priv check + output gate + audit; unregistered tool returns fail-closed envelope.
- `/home/ormastes/dev/pub/simple/test/os/kernel/fs/win_vfs/win_vfs_driver_spec.spl` — AC-4: mount `/win`, readdir app+schema entries, read title bytes, destroy→ENOENT, ACL-deny→EACCES, grep sentinel for encoder imports.
- `/home/ormastes/dev/pub/simple/test/os/compositor/wm_spm_client_spec.spl` — AC-3: same encoded bytes over host + SimpleOS transport; free encoder matches client.
- `/home/ormastes/dev/pub/simple/test/app/simple_process_manager/winfs_shim_host_spec.spl` — AC-4: host shim writes same `/<app>/<wid>/title` layout via shared encoder; grep sentinel for shared-encoder import.

**AC Coverage.**
| AC | Spec files |
|----|------------|
| AC-1 | id_path_spec, store_spec, group_spec, principal_spec |
| AC-2 | fs_encoder_spec, acl_spec, window_record_spec |
| AC-3 | spm_service_spec, wm_spm_client_spec |
| AC-4 | win_vfs_driver_spec, winfs_shim_host_spec, acl_spec |
| AC-5 | output_gate_spec, dispatch_spec |
| AC-6 | content_authority_spec, wiki_tool_spec, approval_broker_spec, dispatch_spec |
| AC-7 | deferred — covered by Phase 7 `bin/simple test` + `build check` run across the above suite + existing regressions |

**Status.** All 16 files are red (no implementation exists). Phase 5 (Engineer) now picks up the impl.

**Coverage markers added.**
- `src/lib/common/privilege/{id_path,store,group,principal}.spl` (via privilege specs)
- `src/lib/nogc_sync_mut/privilege/store_fs.spl` (via store_spec)
- `src/lib/common/win_fs/{window_record,fs_encoder,acl}.spl`
- `src/lib/common/llm/{output_gate,content_authority}.spl`, `src/lib/nogc_sync_mut/llm/notify.spl`
- `src/lib/nogc_sync_mut/mcp/dispatch.spl`
- `src/app/simple_process_manager/{spm_service,privilege_service,window_registry,approval_broker,transport,transport_host,transport_simpleos,wm_spm_client,winfs_shim_host}.spl`
- `src/app/mcp/wiki_keyword/{wiki_tool,register}.spl`
- `src/os/kernel/fs/win_vfs/{win_vfs_driver,win_vfs_mount}.spl`

### 5-implement

#### Wave 5a (shared pure libs + pure llm filter + nogc adapters)

**Date:** 2026-04-18  **Agent:** Engineer (Claude).

**Files created / finalized (absolute paths):**
- `/home/ormastes/dev/pub/simple/src/lib/common/privilege/id_path.spl` (verified from prior session)
- `/home/ormastes/dev/pub/simple/src/lib/common/privilege/principal.spl` (verified)
- `/home/ormastes/dev/pub/simple/src/lib/common/privilege/group.spl` (verified)
- `/home/ormastes/dev/pub/simple/src/lib/common/privilege/authority_token.spl` (verified)
- `/home/ormastes/dev/pub/simple/src/lib/common/privilege/store.spl` (verified)
- `/home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/privilege/store_fs.spl` (verified)
- `/home/ormastes/dev/pub/simple/src/lib/common/win_fs/window_record.spl` (verified)
- `/home/ormastes/dev/pub/simple/src/lib/common/win_fs/fs_encoder.spl` (+ `pub use FsOp` re-export added this wave)
- `/home/ormastes/dev/pub/simple/src/lib/common/win_fs/acl.spl` (verified)
- `/home/ormastes/dev/pub/simple/src/lib/common/llm/output_gate.spl` (authored this wave)
- `/home/ormastes/dev/pub/simple/src/lib/common/llm/content_authority.spl` (authored this wave)
- `/home/ormastes/dev/pub/simple/src/lib/nogc_sync_mut/llm/notify.spl` (authored this wave)

**Phase 3 corrections recorded during implementation:**
1. `AuthorityToken` field is `level:` (not `authority:` as §B loosely wrote) — matches spec usage.
2. `GateDecision` and `ReleaseDecision` are **classes with `kind: text` field**, not enums — required by spec `decision.kind to_equal "..."` assertions. Same shape already landed for `DecodeResult` / `PrincipalResult`.
3. `FsOp` is defined in `lib.common.win_fs.window_record` (not `fs_encoder`). Spec imports from `fs_encoder`, so `fs_encoder.spl` re-exports it via `pub use`.
4. `output_gate.spl` does **byte-level** scanning (pattern table mirrors `app.tools.secret_scan.default_patterns()` shapes) rather than calling `SecretScanner.match_pattern` on `text`. Reason: bootstrap compiler has no `bytes -> text` helper exposed in `src/lib/common/`; only `text.bytes()` exists. Keeps the module pure and off the `src/app/` import graph.
5. `output_gate` keeps **in-memory** notify + audit sink counters (test_mode flag + `test_notify_sink_size` / `test_audit_sink_size` observers) so the spec can verify a Hold would have fired without the pure module doing FS I/O. Real delivery is in `lib.nogc_sync_mut.llm.notify`.
6. `notify.spl` imports `lib.common.security.types` (not `std.security.types`) and `lib.nogc_sync_mut.io.env_ops.{env_get, home}` (not `lib.nogc_sync_mut.env.variables`). `env/variables.spl` uses a Python-style `import` that the bootstrap compiler cannot resolve; `io/env_ops.spl` declares the extern cleanly.

**Wave 5a acceptance status:**
- `bin/simple test test/lib/common/privilege/id_path_spec.spl` → 10/10 Pass
- `bin/simple test test/lib/common/privilege/principal_spec.spl` → 4/4 Pass
- `bin/simple test test/lib/common/privilege/group_spec.spl` → 3/3 Pass
- `bin/simple test test/lib/common/privilege/store_spec.spl` → 5/5 Pass
- `bin/simple test test/lib/common/win_fs/window_record_spec.spl` → 3/3 Pass
- `bin/simple test test/lib/common/win_fs/fs_encoder_spec.spl` → 3/3 Pass
- `bin/simple test test/lib/common/win_fs/acl_spec.spl` → 3/3 Pass
- `bin/simple test test/lib/common/llm/content_authority_spec.spl` → 4/4 Pass
- `bin/simple test test/lib/common/llm/output_gate_spec.spl` → 6/6 Pass

Total: 41/41 it-blocks green. `bin/simple build check` was not run (cost/time) and is deferred to Phase 7 verify per the task rule "don't block on compile failures outside your wave".

**Note on jj parallel race.** During this wave a parallel sstack thread (`spostgre-nvfs-storage`, NVFS Phase 9) executed `jj squash` + `jj restore` against shared paths and transiently wiped the working copy of the wave 5a files and this state file. Files were re-materialized from git object `b4d6ad3318` (which preserved them) and the llm files had Phase-5 fixes re-applied. This matches the "Submodule Race w/ Parallel /dev" + "Sync Skill Clobbers Per-Phase Commits" feedback memories.

**`5-implement` checklist status:** Wave 5a complete (this subsection). Waves 5b (SPM service + kernel VFS + compositor hooks) and 5c (MCP dispatch + dashboard hooks) remain **pending** before `5-implement` can be checked off.

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
