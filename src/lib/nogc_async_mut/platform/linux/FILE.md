# linux — platform variant (src/lib/nogc_async_mut/platform)

Skeleton dir per doc/04_architecture/platform/platform_variant_directory_rule.md
(OS -> ABI -> arch). No code yet; holds only this manifest.

TODO(platform-variant-migration): move here — nothing yet; new linux-specific code lands here instead of a level-0 platform conditional.

## Entries

- **FILE.md** — this manifest.

## Child Manifests

| Path | Description |
|---|---|
| `x86/FILE.md` | linux/x86 variant |
| `x86_64/FILE.md` | linux/x86_64 variant |
| `arm/FILE.md` | linux/arm variant |
| `aarch64/FILE.md` | linux/aarch64 variant |
| `riscv32/FILE.md` | linux/riscv32 variant |
| `riscv64/FILE.md` | linux/riscv64 variant |
