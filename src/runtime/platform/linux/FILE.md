# linux — platform variant (src/runtime/platform)

Skeleton dir per doc/04_architecture/platform/platform_variant_directory_rule.md
(OS -> ABI -> arch). No code yet; holds only this manifest.

TODO(platform-variant-migration): move here — platform_linux.h, async_linux_epoll.c, async_linux_uring.c (from src/runtime/platform/).

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
