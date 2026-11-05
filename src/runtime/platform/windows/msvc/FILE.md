# windows/msvc — platform variant (src/runtime/platform)

Skeleton dir per doc/04_architecture/platform/platform_variant_directory_rule.md
(OS -> ABI -> arch). No code yet; holds only this manifest.

TODO(platform-variant-migration): move here — _MSC_VER-only blocks split out of windows/*.h and *.c.

## Entries

- **FILE.md** — this manifest.

## Child Manifests

| Path | Description |
|---|---|
| `x86/FILE.md` | windows/msvc/x86 variant |
| `x86_64/FILE.md` | windows/msvc/x86_64 variant |
| `aarch64/FILE.md` | windows/msvc/aarch64 variant |
