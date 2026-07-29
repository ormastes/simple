---
name: unstable-build-fixes
description: Use when a Simple bootstrap/native-build is unstable, slow, or failing one bug at a time and needs cache-preserving retries, isolated parallel mini builds, grouped compiler errors, and receipt-sealed incremental promotion.
---

# Unstable Build Fixes

Goal: produce the requested Simple executable without throwing away useful
cache or accepting unsealed build evidence.

## Rules

- Keep one main cache-backed build as source of truth:
  `--cache-dir build/bootstrap/native_cache --mode dynload`.
- Do not delete the cache between retries unless a concrete stale-cache bug is proven.
- Do not run parallel writers into the same cache dir. Use isolated shard caches:
  `build/mini_cache_<entry>`.
- If a source fix lands while a build is still before object output, prefer letting it fail or finish. Restart only when no cache/output can be lost.
- Keep every log under `build/mini_builds/` or `build/native_probe/`.
- Set `SIMPLE_NO_STUB_FALLBACK=1` for every candidate or verification build;
  a binary containing generated unresolved stubs is debug evidence only.

For the active ten-spec SimpleOS shared-font Stage2 scope, do not enter the
Stage3/4 loop. First run `sh scripts/bootstrap/bootstrap-from-scratch.sh
--stop-after-stage2` at a clean pinned checkpoint, then pass its canonical
Stage2 binary and provenance manifest to the only scoped-tool producer:

```bash
CHECKPOINT_SHA=<clean-commit-sha> \
STAGE2_PARENT=<canonical-stage2-simple> \
STAGE2_PARENT_SHA=<sha256> \
STAGE2_PROVENANCE_PATH=<canonical-stage2-provenance.env> \
STAGE2_PROVENANCE_SHA=<sha256> \
STAGE2_FONT_TOOL_ATTEMPT_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/stage2-scoped-tools/attempt-<next-number> \
STAGE2_FONT_TOOL_CACHE_ROOT=build/native_probe/shared-font-stage2-scoped-tools-cache/attempt-<next-number> \
bash scripts/check/build-stage2-font-scoped-tools.shs write
```

It owns the fresh canonical core-C capsule, current standalone runner/docgen
ELF builds, separate caches, and one green/deliberate-red/zero-example runner
plus zero-stub docgen calibration.
A later verifier runs `bash scripts/check/build-stage2-font-scoped-tools.shs
check <attempt-root>` instead of rerunning a green writer. Repairs use a new
numbered attempt/cache and stop after three cycles; full bootstrap is excluded.

## Loop

1. Establish the promotion parent. A Stage 2 parent must have the canonical
   `build/bootstrap/stage2/<triple>/stage2-provenance.env` and `.sha256`, both
   accepted by `bootstrap_stage2_verify_manifest`. For Option-lowering work,
   run `scripts/check/check-native-option-admission-probes.shs` once against
   that exact Stage 2 binary/manifest, checkpoint, and deterministic core-C
   capsule. Its sealed A/B/C result is required; loose probe output is not.
2. Start or keep a diagnostic main build:
   ```bash
   SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib \
     --entry-closure --threads 8 --cache-dir build/bootstrap/native_cache --mode dynload \
     --entry src/app/cli/_CliMain/main_and_help.spl -o build/native_probe/simple
   ```
   This output localizes failures; it is not Stage 3/Stage 4 evidence.
3. Run parallel mini builds with separate caches for early failures:
   - `src/app/cli/bootstrap_main.spl` -> `build/mini_cache_bootstrap`
   - `src/app/cli/native_build_main.spl` -> `build/mini_cache_native_build`
   - `src/app/mcp/main.spl` -> `build/mini_cache_mcp`
4. For each failure, group by the first real error, not warnings.
5. Fix the smallest shared root cause. Add one focused regression.
6. Rerun only failed shards first, with the same shard cache.
7. Rerun the diagnostic build with the same main cache.
8. Promote incrementally through the canonical staged wrapper. For Stage 4,
   `scripts/check/stage4-provenance-receipt.shs write` must own the isolated
   command and transcript while binding the admitted parent, deterministic
   core-C capsule, before/after source and Git state, exclusively locked cache,
   native output, and output hash. Do not create a receipt around an earlier
   loose build.
9. Stop when the requested binary exists, its native format and focused smoke
   pass, and any Stage 4 result has a sealed receipt plus an essential-tools
   smoke result against that exact artifact.

Do not use `--full-bootstrap` as a retry strategy. It is reserved for changed
Rust seed/runtime inputs or a demonstrated capability missing from the admitted
seed; pure-Simple failures stay on the cache-preserving incremental path.

## Patterns

- If `--entry-closure` is CPU-bound before HIR/driver debug output, inspect the
  closure queue first. Shared imports need a queued-set as well as `seen`;
  checking only processed files can enqueue the same module many times.
- If LLVM reaches `llc` or link with an undefined runtime helper, fix the call
  name and declaration together. For example, `get_args`/`get_cli_args` should
  lower to the exported runtime symbol `rt_get_args`, and every text/lib LLVM
  declaration list must include that symbol.
- If a bootstrap fast path mirrors a normal lowering path, preserve the normal
  scope and state side effects (`push_scope`/`pop_scope`, `has` flags, call-frame
  snapshots). Fast paths may avoid fragile payload extraction, but not semantic
  state.

## Error Triage

Use:
```bash
rg -n "error:|FAILED|Failed|native-build worker|Bootstrap LLVM|llc failed|unknown extern|undefined|mismatch" <log>
find <cache-dir> -name '*.o' | wc -l
```

Ignore warning-only output unless it is the only changed behavior.
