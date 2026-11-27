# Simple linker refused every FreeBSD cross-link (no sysroot path)

- **Status:** verification-pending
- **Area:** `src/compiler/70.backend/linker/` (internal:elf, FreeBSD hosted)
- **Lane:** sbsd (2026-11-18)

## Symptom
`SIMPLE_LINKER=internal` could not link a FreeBSD x86_64/aarch64 executable
from a Linux or Windows host:

1. `internal_elf_hosted_target_v1` refused any `os != host_os` link with
   "unsupported cross-host link", even though FreeBSD inputs need no host file.
2. `internal_link_native_with_operations` called `freebsd_hosted_inputs("", …)`,
   so the startup objects and `libc.so.7` were always read from the host `/`.
3. `freebsd_hosted_inputs` required `<root>/libexec/ld-elf.so.1` to exist,
   though the loader is never a link input (only its PT_INTERP path is
   written). Cross sysroots (`~/toolchains/freebsd/{amd64,aarch64}`) ship no
   `/libexec`.

## Fix
- `--sysroot=<dir>` in `NativeLinkConfig.extra_flags` (`internal_elf_sysroot`)
  selects the FreeBSD root; any other OS with `--sysroot` is refused by name.
- `internal_elf_hosted_target_sysroot_v1` admits a cross-host link only for
  `freebsd` with a non-empty sysroot. Linux cross-host stays refused.
- The loader existence check only applies to the host root.

## Tests
- `test/01_unit/compiler/backend/linker/internal_elf_hosted_target_spec.spl`
  — FreeBSD+sysroot admitted on linux/windows hosts; FreeBSD without sysroot
  and Linux with sysroot still refused (red before the fix).
- `test/03_system/app/compiler/feature/item4_freebsd_hosted_spec.spl`
  — loaderless sysroot resolves; PT_INTERP stays `/libexec/ld-elf.so.1`;
  a nonexistent root is still rejected.

## Remaining
Running the linked image on FreeBSD (QEMU x86_64, port 2222) and an aarch64
FreeBSD VM: see the lane report / PR body.
