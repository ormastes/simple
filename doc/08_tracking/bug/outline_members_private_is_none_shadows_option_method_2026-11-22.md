# Private free `fn is_none<T>` in outline_members.spl hijacks `.is_none()` across the compiler closure (2026-11-22)

Status: FIXED in source (this change). The helper was unused and is deleted.

## Symptom

New Phase 1 seed (release `6816f70c47e`), `check-simple-core-runtime-smoke.shs`. The
simple-core archive was produced, but the script's first smoke step failed. That step is
`native-build --runtime-bundle simple-core --entry examples/01_getting_started/hello_native.spl`:

```
error: semantic: private fn `is_none` of module
  src/compiler/10.frontend/treesitter/outline_members.spl
  is not visible to src/compiler/80.driver/driver_hir_cache.spl; mark it `pub` or `export` it
  interpreter: build/essential-apps/p1n-seed/simple.exe (exit code 1)
```

The script exited 1 under `set -e`, with no verdict line. The build log
(`/tmp/simple_core_hello_build.<pid>`) was the only evidence.

## Root cause

`outline_members.spl:41` defined a module-level `fn is_none<T>(v: T) -> bool: v == nil`.
It had no callers. When the seed interprets the pure-Simple driver, it resolves
`driver_hir_cache.spl`'s method calls `x.is_none()` (lines 358, 364, 403, 531, 633) to this
co-compiled free function, uniform-call style. The visibility check then rejects it.

## Fix

Delete the unused helper. Census after the fix: no other module-level `fn
is_none|is_some|unwrap|is_ok|is_err` exists in `src/compiler`, `src/lib` or `src/app`. The same
grep against `HEAD` before the fix finds this one, which is the control.

## Specs

- Reproducing: the hello step of `scripts/check/check-simple-core-runtime-smoke.shs` on the new
  seed. Re-run pending (host time is shared with Phase 3).
- Generalization: the census above. The seed-side question is open: should a private free
  function in an unrelated module ever be a uniform-call candidate for `x.method()` at all?
  That belongs to the seed resolver owner and is not changed here.
