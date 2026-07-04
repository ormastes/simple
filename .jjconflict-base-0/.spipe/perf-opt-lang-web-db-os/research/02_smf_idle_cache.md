# SMF Idle Background Compile + Cache Reuse — Research Findings (AC-7)

**Date:** 2026-06-13  
**Scope:** `src/os/smf/dynsmf_session.spl`, `src/app/startup/dynsmf_autoload.spl`,  
`src/compiler/80.driver/` (watcher, cache, driver_api_interpret), build/dynsmf manifest

---

## Verdict Table

| Feature | Status | Evidence |
|---|---|---|
| **Idle/background compile — dynSMF precompiled libs** | PARTIAL | `dynsmf_session_queue_missing_background_compiles` queues evidence rows with `status="queued"` and `reason="queued:bin/simple compile ..."` but **never spawns the process** — no `rt_process_run`/spawn call in `dynsmf_session.spl` or `dynsmf_autoload.spl`. The command string is purely advisory. |
| **Idle/background compile — watcher daemon (user scripts)** | EXISTS | `WatcherDaemon.generate_smf()` in `src/compiler/80.driver/watcher/watcher_daemon.spl:146` calls `compile_to_smf_with_options` and `update_smf_manifest_entry` on file-change events. Runs in a poll loop. Separate from dynSMF precompiled-lib lane. |
| **Unchanged-script cache reuse (`simple run`)** | EXISTS | `try_load_smf_cached` in `src/compiler/80.driver/driver_api_interpret.spl:27` checks `build/smf/manifest.sdn` (via `load_smf_manifest_default` + `smf_manifest_find`), then calls `validate_smf` (source SHA-256 + options_hash + dep interface hashes) — returns cached SMF on fresh, re-interprets on stale/missing. |
| **Stale-source invalidation (content-hash)** | EXISTS | `validate_smf` → `validate_smf_with_deps` in `src/compiler/80.driver/cache/cache_validator.spl:103` reads SMF header `source_hash`, hashes current source via `rt_hash_sha256`, returns `STALE "source hash changed"` on mismatch. Also checks dep interface hashes (Level 4). |
| **Stale-source invalidation (dynSMF precompiled lane)** | PARTIAL | `dynsmf_artifact_has_smf_magic` checks `SMF\0` magic bytes only (lines 147–160 of `dynsmf_session.spl`). **No content-hash** — a stale-but-magic-correct artifact is treated as ready. `dynsmf_session_record_background_compile_for_status` skips queuing if `artifact_ready`, so a stale precompiled SMF is silently reused. |
| **ABI/accessor-change invalidation** | PARTIAL | SHB Level 2 (`shb_cache.spl`) tracks interface_hash; `validate_smf_with_deps` checks dep interface hashes for user scripts. The dynSMF precompiled-lib lane has **no interface-hash check** — magic bytes are sufficient to mark ready. |
| **Spec coverage** | PARTIAL | `dynsmf_session_spec.spl` covers manifest, build-plan generation, background-compile evidence queuing, autoload evidence. `dynsmf_autoload_policy_spec.spl` covers policy args/env, queued-then-fail on missing artifact, skip-all, per-id disable. **No spec** for: (a) actual background process spawn, (b) unchanged-script cache reuse (`try_load_smf_cached` path), (c) stale-source cache miss for user scripts, (d) stale precompiled SMF miss for dynSMF lane. |

---

## dynsmf_session

**File:** `src/os/smf/dynsmf_session.spl`

- `DynSmfSession` holds `session_id`, `generation`, `policy`, `loaded: []`, `evidence: []`.
- `dynsmf_session_new` (line 262): constructs empty session.
- `dynsmf_default_manifest` (line 68): 7 entries (`file_io`, `net_io`, `render2d`, `web_renderer`, `gui_renderer`, `tui_renderer`, `ui_html`), all `artifact_kind="precompiled_smf"`, all `default_autoload=true`.
- `dynsmf_build_plan` (line 110): assembles `command = "bin/simple compile <src> -o <out>"` — **string only, never executed here**.
- `dynsmf_session_queue_missing_background_compiles` (line 222): calls `_request_background_compiles_from_statuses` with `record_ready=false, record_disabled=false`. Pushes `DynSmfEvidenceRow(status="queued", reason="queued:<command>")` into `session.evidence`. **No process spawn.**
- `dynsmf_artifact_status` (line 163): reads file bytes, checks `SMF\0` magic (bytes 83,77,70,0). No content hash.
- `dynsmf_session_autoload_checked` (line 346): iterates manifest, calls `dynsmf_session_load_checked` for each `default_autoload=true` entry → `smf_dlopen_checked` → fails if artifact missing/invalid-magic.

**Key gap:** `dynsmf_background_compile_action()` returns the string `"compile_background"` (line 137–138). The session records that a compile *should* happen but the caller (`dynsmf_startup_session_for_manifest_from_values`) never dispatches the queued commands to a subprocess.

---

## Autoload Policy

**File:** `src/app/startup/dynsmf_autoload.spl`

- `dynsmf_startup_session_for_manifest_from_values` (line 13):
  1. Build policy from args/env (`--no-dynsmf`, `SIMPLE_DYNSMF=0`, `--disable-dynsmf=ids`).
  2. Call `dynsmf_session_queue_missing_background_compiles` — records queued evidence, **no spawn**.
  3. Call `dynsmf_session_autoload_checked` — tries `smf_dlopen_checked`; fails closed if artifact absent or magic invalid.
- Fail-closed: a missing or corrupted `.smf` file records `status="failed", reason="artifact_missing_file"` and the library is NOT loaded. This is correct behavior.
- `dynsmf_startup_session` (line 28): reads `SIMPLE_DYNSMF` and `SIMPLE_DYNSMF_DISABLE` env vars via `rt_env_get`.

---

## Cache / Invalidation Path (User Scripts)

**Files:**
- `src/compiler/80.driver/driver_api_interpret.spl` — `interpret_file` + `try_load_smf_cached`
- `src/compiler/80.driver/watcher/smf_manifest.spl` — `SmfManifest` at `build/smf/manifest.sdn`; `SmfManifestEntry` holds `source_hash: i64`, `compiled_at`, backend/opt metadata
- `src/compiler/80.driver/cache/cache_validator.spl` — `validate_smf` → `validate_smf_with_deps`

**Flow for `simple run <file.spl>`:**
1. `interpret_file(path)` → `try_load_smf_cached(path)`
2. Lookup `build/smf/manifest.sdn` for entry keyed by `source_path`.
3. If found and `.smf` exists: call `validate_smf(source_path, smf_path, compile_options_hash_zero())`.
4. `validate_smf_with_deps` reads SMF header `source_hash`, hashes current source with `rt_hash_sha256`, compares. Stale → re-interpret. Fresh → `CompileMode.SmfExec` (load cached SMF).
5. Dep interface hashes also checked (Level 4 in `cache_validator.spl`).

**Watcher daemon** (`src/compiler/80.driver/watcher/watcher_daemon.spl:146`):
- `generate_smf(req)` → `compile_to_smf_with_options` + `update_smf_manifest_entry` — writes the manifest entry with current `source_hash`.
- Triggered by file-change events in the poll loop (`process_file_changes`).
- Also handles explicit `WatcherRequestKind.Smf` daemon requests.

**Cache invalidation IS enforced** for user scripts via source hash mismatch. Public API changes propagate through SHB interface_hash dependency chain.

---

## Specs

| Spec | What it covers | Gap |
|---|---|---|
| `test/01_unit/os/smf/dynsmf_session_spec.spl` | Manifest entries, build-plan commands, background-compile evidence rows (queued/skipped/failed), policy args/env, autoload evidence, unload, stale symbol, reload generation | No spec for: actual background process spawn; cache reuse; stale precompiled SMF miss |
| `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl` | Policy skip-all, per-id disable, 7-lib autoload (calls script to build artifacts if missing), queued-then-fail on missing artifact, `--dynsmf-status` output | No spec for: background spawn; unchanged-script reuse |
| `test/02_integration/app/startup_argparse_mmap_perf/` | (not inspected — focused on argparse/mmap, not SMF cache) | Out of scope for AC-7 |

---

## What to BUILD

### 1. Actually dispatch the queued background-compile commands (PARTIAL → EXISTS)
**What:** After `dynsmf_session_queue_missing_background_compiles`, iterate `evidence` rows with `status="queued"` and spawn each `plan.command` asynchronously (via `process_spawn_async` already used in `src/app/mcp/dap_bridge.spl`). Add `status="dispatched"` evidence update.  
**Where:** `src/app/startup/dynsmf_autoload.spl` — add `dynsmf_startup_dispatch_background_compiles(session)` after autoload; or wire into the watcher-daemon `WatcherRequestKind.Smf` path.  
**Spec needed:** integration test asserting the `.smf` artifact is produced after startup + idle period for a manifest entry that was absent at launch.

### 2. Content-hash invalidation for dynSMF precompiled lane (PARTIAL → EXISTS)
**What:** `dynsmf_artifact_status` currently accepts any artifact with valid `SMF\0` magic. Add source-hash comparison: hash the `entry.source_module` source file and embed it in the artifact path lookup (or read from a companion `.smf.hash` sidecar). Reject artifacts whose embedded/sidecar hash doesn't match current source.  
**Where:** `src/os/smf/dynsmf_session.spl:163` (`dynsmf_artifact_status` function) + `scripts/check/check-low-dependency-dynsmf-build-plans.shs` to write sidecar.  
**Spec needed:** spec asserting that a recompiled-but-magic-valid stale artifact triggers re-queue (not `artifact_ready` skip).

### 3. Spec: unchanged-script cache-reuse + stale-miss for user scripts (coverage gap)
**What:** `try_load_smf_cached` exists and works but has zero spec coverage. Add a unit/integration spec: (a) run script → produces SMF in manifest, (b) run again unchanged → loads cached SMF (check log line `[interp] Loading pre-compiled SMF:`), (c) modify script → cache misses → re-interprets.  
**Where:** new `test/02_integration/app/simple/smf_cache_reuse_spec.spl`.  
**Also needed:** verify `validate_smf` stale path is hit when source changes (can use a synthetic manifest entry with wrong hash).

---

## Risks

1. **Background spawn never fires today** — the dynSMF precompiled libs may not be present in fresh checkouts, causing 7 autoload failures silently. The queued evidence gives the right command string but no executor.
2. **Stale precompiled SMF accepted** — if a developer edits `src/lib/nogc_sync_mut/io/file.spl` without rebuilding `build/dynsmf/file_io.smf`, the old artifact is loaded (magic check passes). No source-hash guard on this lane.
3. **`SIMPLE_MCP_USE_CACHE=1` required for SMF path in MCP** — per memory note, MCP wrappers run `.spl` by default; `try_load_smf_cached` is never reached unless the env var opts in. AC-7 proof must be demonstrated in interpreter mode with watcher running, not MCP.
