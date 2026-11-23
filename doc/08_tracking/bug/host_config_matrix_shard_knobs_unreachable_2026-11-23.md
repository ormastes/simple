# Host config cannot set the Stage 2 matrix / Stage 3 shard workarounds (W36)

- **Date:** 2026-11-23
- **Status:** FIXED (host-config keys added; underlying W27/W32 defects remain OPEN)
- **Ledger:** W36 (`C:/dev/simple-release-boot-20261122/build/rboot/WORKAROUNDS.md`),
  depends on W27 (shard workers AV on warm `.fpc` read-back, root cause OPEN)
  and W32 (4139-module MIR workers exhausted commit).
- **Host:** DESKTOP-VMF96U6 (Windows / Git Bash / MSVC)

## Symptom

After Stage 2 admission, `bootstrap-from-scratch.sh` runs the Stage 2
compiler-test / phase verification matrix (full CLI + tests). On this host the
matrix needs `SIMPLE_FRONTEND_CACHE=0` (W27) and a larger
`SIMPLE_MIR_SHARD_COUNT` with a single large MIR worker (W32). The host config
(`config/host/<hostname>.sdn`, read by
`scripts/bootstrap/lib/host-bootstrap-settings.shs`) had no keys for them, so
every unattended run hit the defects unless an operator exported env vars by
hand.

## Second defect found while fixing: the matrix never saw the caller's frontend cache

`bootstrap_cache_enable_persistence` (`scripts/bootstrap/bootstrap-cache-lineage.shs:271`,
called from `bootstrap-from-scratch.sh` `bootstrap_prepare_phase_cache`) exports
`SIMPLE_FRONTEND_CACHE=1` into the main shell before the matrix subshell runs.
The Stage 3 launch already used the value captured at entry
(`bootstrap_caller_frontend_cache`, `bootstrap-from-scratch.sh:26`), but the
matrix did not, so even a hand-exported `SIMPLE_FRONTEND_CACHE=0` was replaced
by `1` for every matrix tool row. The matrix subshell now re-applies the
captured caller/host value.

## Fix

`scripts/bootstrap/lib/host-bootstrap-settings.shs`:

| key | env var | values |
|---|---|---|
| `frontend_cache` (existing schema key) | `SIMPLE_FRONTEND_CACHE` | `on`/`off` -> `1`/`0` |
| `mir_sharding` | `SIMPLE_MIR_SHARDING` | `0`/`1` |
| `mir_shard_count` | `SIMPLE_MIR_SHARD_COUNT` | `1..128` |
| `mir_shard_worker_kib` | `SIMPLE_MIR_SHARD_WORKER_KB` | positive integer |

Applied only when the env var is unset (explicit env wins); printed with
`(source: host config <key>)`; an invalid value in any layer is a hard error
naming the key (the `host-env.shs --get` invalid-value warning is read, as
`tree-rss-policy.shs bootstrap_tree_rss_knob` does). The keys are validated in
`scripts/setup/host-env.shs host_config_valid` too.

`frontend_cache` is `on|off` in the existing schema (`host-env.shs`,
`src/lib/common/config_core/host_config.spl:71`), so the host file uses
`frontend_cache: off`; a `0` would be rejected.

Lanes and consumers:

- Stage 2 matrix: `bootstrap-from-scratch.sh` matrix subshell calls
  `bootstrap_host_apply_matrix_settings` and re-exports the caller/host
  frontend value before `bootstrap_tree_rss_whole_build_export` (which keeps a
  set `SIMPLE_MIR_SHARD_WORKER_KB`, `tree-rss-policy.shs:1158`). All four
  variables cross into each tool row via
  `bootstrap_phase_c_tool_row_environment_keys`
  (`phase-c-backend-commands.shs:63` FRONTEND_CACHE, `:66` SHARDING +
  SHARD_COUNT, `:68` SHARD_WORKER_KB); `bootstrap-phase-verification.shs:1075`
  routes full tools through the Stage 3 dispatcher when SHARDING=1.
- Stage 3 in `bootstrap-from-scratch.sh`: applied before the W24/W27
  pass-through that hashes/transcribes SHARDING and the caller frontend value.
- `resume-stage3-from-admitted.sh`: applied before the shard-count read and the
  W24/W27 pass-throughs; forwarded to the worker on the explicit `env` lines.

Known limit (not fixed here): `SIMPLE_MIR_SHARD_WORKER_KB` is not part of the
Stage 3 hashed/transcribed vector, so `mir_shard_worker_kib` reaches the Stage 2
matrix only. `SIMPLE_MIR_SHARD_COUNT` is consumed by Stage 3 only on the
per-file and interface-HIR lanes.

`config/host/DESKTOP-VMF96U6.sdn`: `frontend_cache: off`, `mir_sharding: 1`,
`mir_shard_count: 16`, `mir_shard_worker_kib: 31457280`.

## Specs

- Reproduction + generalization:
  `scripts/bootstrap/tests/host-config-matrix-shard-knobs-test.shs` (27 checks:
  no key = unchanged; key = exported; env wins per key; seven invalid values
  each a hard error naming the key; invalid host value ignored when env set;
  committed DESKTOP-VMF96U6 values validate; lane-order text contracts; the
  tool-row allowlist forwards all four). Wired as
  `local-host-config-matrix-shard-knobs` in `config/check/must_check_gates.sdn`.
- Regression: `scripts/bootstrap/tests/stage3-mir-sharding-frontend-cache-passthrough-test.shs`
  (32 cases) and `sh scripts/setup/host-env.shs --selftest` (11) stay green.

## Unblock for removal

Delete the four keys from the per-host file once W27 (warm `.fpc` read-back AV)
and W32 (MIR worker commit exhaustion) are fixed at the root.
