# windows/mingw — platform variant (src/runtime/platform)

Skeleton dir per doc/04_architecture/platform/platform_variant_directory_rule.md
(OS -> ABI -> arch). No code yet; holds only this manifest.

TODO(platform-variant-migration): move here — __MINGW32__-only blocks split out of windows/*.h and *.c.

## Entries

- **FILE.md** — this manifest.

## Child Manifests

| Path | Description |
|---|---|
| `x86/FILE.md` | windows/mingw/x86 variant |
| `x86_64/FILE.md` | windows/mingw/x86_64 variant |
| `aarch64/FILE.md` | windows/mingw/aarch64 variant |
