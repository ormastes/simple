# macos — platform variant (src/lib/nogc_sync_mut/sosix)

Skeleton dir per doc/04_architecture/platform/platform_variant_directory_rule.md
(OS -> ABI -> arch). No code yet; holds only this manifest.

TODO(platform-variant-migration): move here — nothing yet; new macos-specific code lands here instead of a level-0 platform conditional.

## Entries

- **FILE.md** — this manifest.
- **contained_write_v1.spl** — typed refusal for contained write/read grants (`contained-write-unimplemented-macos`).
- **app_container_v1.spl** — typed refusal for the app sandbox (`app-sandbox-unimplemented-macos`).
- **containment_v1.spl** — typed refusal for SOSIX containment (`containment-unimplemented-macos`).

## Child Manifests

| Path | Description |
|---|---|
| `x86_64/FILE.md` | macos/x86_64 variant |
| `aarch64/FILE.md` | macos/aarch64 variant |
