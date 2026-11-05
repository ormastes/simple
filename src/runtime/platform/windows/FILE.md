# windows — platform variant (src/runtime/platform)

Skeleton dir per doc/04_architecture/platform/platform_variant_directory_rule.md
(OS -> ABI -> arch). No code yet; holds only this manifest.

TODO(platform-variant-migration): move here — platform_win.h, async_windows.c, runtime_win_*.h, windows_*.h, runtime_windows_private_atomic.h, test_platform_win.h.

## Entries

- **FILE.md** — this manifest.

## Child Manifests

| Path | Description |
|---|---|
| `mingw/FILE.md` | windows/mingw variant |
| `msvc/FILE.md` | windows/msvc variant |
