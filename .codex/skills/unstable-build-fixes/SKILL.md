---
name: unstable-build-fixes
description: Use when a Simple bootstrap/native-build is unstable, slow, or failing one bug at a time and needs cache-preserving retry loops, isolated parallel mini builds, grouped compiler errors, and repeat fix/rebuild cycles until a Simple executable is produced.
---

# Unstable Build Fixes

Goal: produce the requested Simple executable without throwing away useful cache.

## Rules

- Keep one main cache-backed build as source of truth:
  `--cache-dir build/bootstrap/native_cache --mode dynload`.
- Do not delete the cache between retries unless a concrete stale-cache bug is proven.
- Do not run parallel writers into the same cache dir. Use isolated shard caches:
  `build/mini_cache_<entry>`.
- If a source fix lands while a build is still before object output, prefer letting it fail or finish. Restart only when no cache/output can be lost.
- Keep every log under `build/mini_builds/` or `build/native_probe/`.

## Loop

1. Start or keep the main build:
   ```bash
   bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib \
     --entry-closure --threads 8 --cache-dir build/bootstrap/native_cache --mode dynload \
     --entry src/app/cli/main.spl -o build/native_probe/simple
   ```
2. Run parallel mini builds with separate caches for early failures:
   - `src/app/cli/bootstrap_main.spl` -> `build/mini_cache_bootstrap`
   - `src/app/cli/native_build_main.spl` -> `build/mini_cache_native_build`
   - `src/app/mcp/main.spl` -> `build/mini_cache_mcp`
3. For each failure, group by the first real error, not warnings.
4. Fix the smallest shared root cause. Add one focused regression.
5. Rerun only failed shards first, with the same shard cache.
6. Rerun the main build with the same main cache.
7. Stop when `build/native_probe/simple` or the requested deployed `bin/simple` exists.

## Error Triage

Use:
```bash
rg -n "error:|FAILED|Failed|native-build worker|Bootstrap LLVM|llc failed|unknown extern|undefined|mismatch" <log>
find <cache-dir> -name '*.o' | wc -l
```

Ignore warning-only output unless it is the only changed behavior.
