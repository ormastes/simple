# native-build --backend llvm: "llc not found" x1427 although llc.exe is on PATH

Registered 2026-11-16. Status: fix-implemented-verification-pending. Severity P2.

## Symptom

In a 1,542-module `native-build --backend llvm` run by the frozen Phase 2
compiler (pin `18a1f28937c2`), codegen reported 1,427 x `llc not found` while
`llc.exe` exists on PATH (msys2 clang64; llvm-mingw ships no llc). Free memory
was about 3 GB at the time.

## What the code does (read at origin/release/1.0.0 115bd321a44)

- `src/compiler/70.backend/backend/llvm_backend_tools.spl:466-470`: per AOT unit,
  `val llc = find_llc()`; `val clang = if llc == "": find_clang() else: ""`;
  `if llc == "" and clang == "": return llvm_object_stage_fail(..., "llc not
  found", 1)`. So the message is emitted when BOTH llc and clang resolve to the
  empty string. The text does not say whether a probe failed or the tool is
  absent.
- `src/compiler/95.interp/interpreter/llvm/tools.spl`: `find_llc()` (line 192)
  calls `_find_tool([...])` (line 98). `_find_tool` HAS a per-process cache
  (lines 87-96, 120-137, commit 73a12be2d25, 2026-10-25, an ancestor of the
  pin): a hit is cached for the process lifetime, but a miss is cached only as a
  counter and retried until `_FIND_TOOL_MAX_MISSES = 3`, after which `""` is
  cached permanently. This contradicts "re-probes per unit"; the probe is not
  per unit once cached.
- `_find_tool_discover` (line 139) order: env dirs (`SIMPLE_LLVM_BIN`,
  `LLVM_SYS_231_PREFIX`, `SIMPLE_LLVM_WIN_ROOT_23`, `LLVM_SYS_180_PREFIX`) with
  `file_exists` + `_tool_runs` (spawn `--version`, exit 0 required); then per
  candidate: in-process PATH scan (`backend_tool_on_path`) + `_tool_runs`; then
  `where <candidate>` via a shell subprocess, each hit run with `--version`.
  Any failed spawn (`process_run` nonzero/-1) is indistinguishable from "tool
  absent" and yields `""`.

## Hypothesis (not confirmed)

Under memory pressure the `--version` / `where` subprocess spawn fails
transiently. The first 3 calls that fail (possibly concurrent units across
workers, or any three early failures) exhaust the bounded retry, and `""` is
then cached for the rest of the process, producing the long run of
`llc not found`. That would explain why a count in the thousands appears even
though the cache exists: a few transient failures become permanent. If the
build runs codegen in several worker processes, each has its own cache.

## Workaround

Pin `SIMPLE_LLVM_BIN=<dir containing llc.exe>`. With it set, a rerun showed 0
occurrences through HIR+MIR; codegen confirmation is pending.

## Proposed fix (proposal only)

1. Resolve each tool once per process at startup (before heavy allocation) and
   cache the success; never cache a transient failure as a permanent `""`.
2. Distinguish "probe failed" (spawn error / nonzero `--version`) from "not
   found" (no candidate file exists) and report it in the message, including
   the candidate path tried and exit code.
3. Prefer a cheap non-spawn existence check, and retry a failed probe with
   backoff before giving up.

## Status

`fix-implemented-verification-pending` (2026-11-18).

### Implementation Summary

- `src/compiler/95.interp/interpreter/llvm/tools.spl`:
  - Added `"SIMPLE_LLVM_MINGW_ROOT"` (`/bin`) to `_env_tool_dirs()` via `env_tool_dirs_from` / `env_tool_dirs()` so llvm-mingw `clang.exe` resolves directly without spawning `where`.
  - Separated "no candidate file exists on disk" from "candidate file exists on disk (`file_exists(path)` or `_tool_path_is_absolute(on_path)` true) but `_tool_runs(path)` (`--version`) failed transiently" via `_find_tool_discover_outcome`, `_probe_candidate_paths`, and pure helpers (`tool_probe_evaluate_observations`, `tool_probe_decide_counts`, `tool_probe_decide`, `tool_cache_should_reuse_counts`, `tool_cache_should_reuse`, `format_tool_probe_diagnostic_with_cap`, `format_tool_probe_diagnostic`).
  - Added `pub fn last_tool_probe_diagnostic() -> text`, `find_tool_cache_check`, `find_tool_cache_record_with_persist`, `find_tool_cache_record`, `find_tool_cache_commit_probe`, `find_tool_cache_lock_is_free`, and `reset_find_tool_cache`:
    - Transient `--version` failures on an existing candidate record the failed candidate path(s) and NEVER increment `_find_tool_cache_misses` (`_FIND_TOOL_MAX_MISSES = 3`), instead using a separate higher cap `_FIND_TOOL_MAX_TRANSIENT_MISSES = 16` so transient spikes recover while permanently broken on-disk binaries stop re-probing after 16 attempts; genuinely absent binaries (`exists = false`) still stop retrying after `_FIND_TOOL_MAX_MISSES = 3`.
    - Protected all shared cache arrays (`_find_tool_cache_*`) and `_last_tool_probe_diagnostic` reads/writes with an eagerly module-initialized (`val _find_tool_cache_lock_handle = _find_tool_cache_lock_init()`) process-lifetime `rt_atomic_int_*` CAS spinlock (`_find_tool_cache_lock_acquire`/`_release`, cross-engine across Rust seed, C runtime, Core Simple, and Stage2 AOT) while running `_find_tool_discover_outcome` unlocked and committing via double-checked `find_tool_cache_commit_probe` so concurrent OS worker threads in `group_native_llvm_*` never race on cold init or cache updates.
    - `find_tool_cache_check` remains strictly read-only on `_last_tool_probe_diagnostic`, and strict-mode `Ok(path)` clears a stale `_last_tool_probe_diagnostic` under lock when `tool_cache_can_persist()` is true.
    - `find_tool_cache_commit_probe` / `find_tool_cache_record` / strict-mode diagnostic updates check `tool_cache_can_persist()` (`transient_array_scope_state_v1() == 0`) so scope-owned strings and array buffers are never published into process-lifetime globals inside an active `transient_scope`.

### Spec Evidence

- Unit spec: `test/01_unit/compiler/interp/llvm_tool_probe_transient_cache_spec.spl` (interpreter mode via `C:/dev/p3_goal_20261116/phase1_artifacts/simple.exe`, `--mode=interpreter --no-session-daemon --sequential --no-db --no-cache --assert-ran --fail-fast`): `Results: 13 total, 13 passed, 0 failed`.
- Sibling unit specs (interpreter mode):
  - `test/01_unit/compiler/95.interp/llvm_find_tool_cache_spec.spl`: `Results: 1 total, 1 passed, 0 failed`.
  - `test/01_unit/compiler/backend/llvm_env_get_local_owner_spec.spl`: `Results: 4 total, 4 passed, 0 failed`.
  - `test/01_unit/compiler/backend/group_native_thread_capability_spec.spl`: `1 passed, 1 failed` (existing interpreter visibility failure on `_group_native_llvm_slot_worker_v1` in `group_native_thread_capability.spl`, unrelated to `tools.spl`).
- Ratchet check (`scripts/check/check-nil-outside-unsafe-added.shs --rank`): `0` violations in both `src/compiler/95.interp/interpreter/llvm/tools.spl` and `test/01_unit/compiler/interp/llvm_tool_probe_transient_cache_spec.spl`.
- Diff check (`git diff --check`): clean (exit 0).
- Full native-build verification under Phase 2 compiler load remains pending.
