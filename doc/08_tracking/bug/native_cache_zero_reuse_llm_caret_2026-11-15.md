# native-build reported 0 reused / 712 rebuilt for llm_caret despite warm cache

Status: closed (not a defect)
Date: 2026-11-15

## Report
`SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_INCREMENTAL=1 simple.exe native-build src/app/llm_caret/main.spl --cache-dir build/nb/cache`
printed `[native-build] compiled=712 reused=0 failed=0 scope=scope-6acac0b26822bca3`
(`build/nb/caret_reverify_build.log`, 2026-11-15 05:34).

## Investigation
- Cache scope is not the cause. `cache_scope_segment()` = hash(`SIMPLE_CACHE_SCOPE` or `default`, `compiler_fingerprint()`),
  and `compiler_fingerprint()` hashes only the bytes of `current_exe`. It folds no cwd, PATH, timestamp or source-tree input.
  `build/nb/cache` has 3 scope dirs, one for each seed binary used (14:27, 18:02, 22:44). The seed was rebuilt at 22:42.
  The warm 22:43-22:47 objects (1146) and the 05:33 objects (711) are all in the SAME scope `scope-6acac0b26822bca3`.
- `GlobalBuildFingerprint::combined()` folds the producer (exe bytes), opt-level, entry-closure, target, linker script and instrumentation.
  None of these is volatile between runs.
- Between the warm build (worktree at `cda4d2d059a`, 22:47) and the cold-looking one (`cd0630ec257`, 05:32) the worktree switched branches.
  80 files under `src/lib`, `src/app/llm_caret` and `src/compiler` changed, and several of them were deleted (`observer/*`, `key_resolver.spl`, ...).
  The per-module interface slices therefore changed widely, so a full rebuild is plausible and correct.
- Decisive check: an immediate rebuild with the same seed and the same cache, after a 4-file source delta (`cd0630ec257` -> `6c93df25b5d`), reused objects:

```
[native-build] compiled=2 reused=710 failed=0 scope=scope-6acac0b26822bca3
[native-incremental] 710 reused / 2 rebuilt
```

## Conclusion
Incremental reuse works. The 0-reuse run came from a real source-tree change (a branch switch), not from a key component that changes between identical-seed runs.

Gap, not filed as a defect: by default the build does not print *why* nothing was reused (`describe_change` output). That made this look like a cache bug.
