# windows — platform variant (src/lib/nogc_sync_mut/sosix)

Skeleton dir per doc/04_architecture/platform/platform_variant_directory_rule.md
(OS -> ABI -> arch). No code yet; holds only this manifest.

TODO(platform-variant-migration): move here — windows_memory_v1.spl.

## Entries

- **FILE.md** — this manifest.
- **security_abi_v1.spl** — advapi32 token/SID/ACL externs and bounded helpers (Win64).
- **restricted_identity_v1.spl** — restricted low-integrity token and scope SID for contained children.
- **contained_write_v1.spl** — low-label write grant and reader-SID read grant (Windows body).
- **app_container_v1.spl** — per-scope AppContainer launch with no capabilities, grants only on listed dirs, profile deleted at teardown (identity `app-sandbox`).
- **app_container_confinement_probe_v1.spl** — evidence-only inside/outside read probe over app_container_v1 (runs both sandbox runs itself; sets no capability flag).
- **containment_v1.spl** — SOSIX containment variant: support, start, poll, cancel, collect, qualify, memory-cap evidence.
- **containment_launch_v1.spl** — job + restricted-token launch core over the process owner (internal).
- **containment_qualify_v1.spl** — nine-canary qualify op with paired positive controls (internal).
- **containment_memory_v1.spl** — memory-cap evidence over lane E probe (internal).

## Child Manifests

| Path | Description |
|---|---|
| `x86/FILE.md` | windows/x86 variant |
| `x86_64/FILE.md` | windows/x86_64 variant |
| `aarch64/FILE.md` | windows/aarch64 variant |
