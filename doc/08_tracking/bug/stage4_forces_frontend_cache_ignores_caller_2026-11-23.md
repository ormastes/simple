# Stage 4 forces SIMPLE_FRONTEND_CACHE=1, ignoring the caller (2026-11-23)

**Status:** fixed (this change). **Severity:** blocks the Windows MSVC
full-CLI relink under the W24/W27 workaround.

## Symptom

On Windows MSVC, MIR shard workers AV reading back the warm frontend parse
cache (`stage3_surface_build_av_items_spl_warm_frontend_cache_2026-11-22.md`,
root cause OPEN). `SIMPLE_FRONTEND_CACHE=0` is the only working configuration
(9/9 shards). PR #10918
(`stage3_resume_drops_mir_sharding_frontend_cache_env_2026-11-23.md`) made the
Stage 3 lanes honour it, but `bootstrap-from-scratch.sh`'s Stage 4 launch
(`bootstrap_native_build_main`, used for both the release and debug-xray
full-CLI builds) hard-coded `SIMPLE_FRONTEND_CACHE=1`, so a caller's `=0` was
silently overridden at Stage 4. The Stage 4 cache context
(`prepare_native_cache stage4|stage4-debug` -> `bootstrap_cache_native_environment`)
also hard-coded `=1`.

## Fix

- Stage 4 entry derives `stage4_frontend_cache` from the entry-time capture
  `bootstrap_caller_frontend_cache` (Stage 2 cache setup has since exported
  `=1`), not from `stage3_frontend_cache` (`--resume-stage4` skips Stage 3).
  unset -> `1` (pinned, byte-for-byte); `0|1` -> used; anything else -> hard
  error before any Stage 4 work.
- The launch env and the stage4/stage4-debug cache context use that value.
- A caller value is transcribed once into the Stage 4 build log
  (`stage4-frontend-cache: SIMPLE_FRONTEND_CACHE=<v>`; the log is already
  hashed into the provenance) and written as `stage4_frontend_cache=<v>` into
  `simple.provenance.env`. Unset writes neither, so log shape and provenance
  bytes are unchanged.
- `stage4_verify_candidate_provenance_generic` calls
  `stage4_verify_frontend_cache_binding`: absent key = `1` and no log line;
  present key must be `0|1` with exactly one agreeing log line; a duplicated
  key is a hard failure, never "absent".

Selftest: `scripts/bootstrap/tests/stage4-frontend-cache-passthrough-test.shs`
(28 cases; text slices of the real scripts, no compiler), wired as
`local-stage4-frontend-cache-passthrough` in `config/check/must_check_gates.sdn`.

## Not changed (same class, follow-ups)

These still pin `SIMPLE_FRONTEND_CACHE=1` and do not honour the caller:

- `bootstrap-from-scratch.sh` stage4b-ui-backend and stage5 (MCP) cache
  contexts; their launches inherit the `=1` exported by
  `bootstrap_cache_enable_persistence` (`bootstrap-cache-lineage.shs:271`).
- `continue-macos-self-host-chain.shs` (macOS lane, not affected by the
  Windows AV) and `prepare-provisional-manager-images.shs`.

Not verified end-to-end: no build was run (a Stage 3 was in progress on the
host); evidence is `sh -n` plus the selftest and mutation checks.
