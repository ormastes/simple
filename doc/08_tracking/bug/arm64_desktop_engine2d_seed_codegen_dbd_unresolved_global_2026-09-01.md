# arm64 `arm64-desktop-engine2d` media phase: seed native codegen cannot compile two `src/os/apps/dbd/` bodies (2026-09-01)

Status: **OPEN**. Fifth blocker in the chain behind the arm64 WM+Vulkan pixel
gate. Found after clearing three earlier prerequisites in a fresh
`origin/main` worktree.

## Prerequisites cleared first (each was a separate hard stop)

1. `build/os/sysroot-aarch64/lib/crt0.o` missing.
   `sh scripts/os/simpleos-sysroot-aarch64.shs` -> rc 0,
   `[sysroot-aarch64] done`. (Confirms the `wchar.h` `__WCHAR_TYPE__` fix.)
2. `build/os/simple-core-simpleos-aarch64/libsimple_runtime.a` missing.
   `SIMPLE_BINARY=<fresh seed> sh scripts/os/simpleos-core-archive.shs --target
   aarch64-unknown-simpleos --out-dir build/os/simple-core-simpleos-aarch64
   --backend cranelift` -> `parts_built=19 parts_failed=0`, rc 0.
   (`--backend llvm`, the script default, still fails every part.)
3. The payload build selected a compiler with the **stale** parser and died with
   `failed to parse src/os/apps/dbd/dbd.spl during discovery: expected
   expression, found Newline`. Cleared by
   `SIMPLE_BUILD_COMPILER=<fresh seed>`, an escape
   `scripts/lib/simple-compiler-select.shs:269` honours explicitly (it warns
   `artifacts built with it will FAIL the provenance guards` — accepted here,
   because this lane is a firmware-handover probe, not an attested artifact).

## The blocker

With the fresh seed selected, the parse error is gone and the failure moves to
**native codegen**:

```
[CODEGEN BODY] Function 'DbdProvisioningOwnerV1.ready' body compilation failed:
  GlobalLoad: unresolved identifier 'provider'
  (not a global, function, const-data name, or import)
[CODEGEN BODY] Function 'DbdLiveClientSessionV1.create' body compilation failed:
  GlobalLoad: unresolved identifier 'DbdTransactionOwnerV1'
  (not a global, function, const-data name, or import)
...
[scenario][arm64-desktop-engine2d] phase=media FAILED   (rc=1)
```

Both sources are ordinary, valid Simple:

- `src/os/apps/dbd/dbd_provisioning.spl:114` — `provider.configured` inside
  `pub fn ready()`, i.e. **implicit-self field access** in a class method.
- `src/os/apps/dbd/dbd.spl:208` — `DbdTransactionOwnerV1.new()`, a **static
  call on a class imported by `use`** at `:45` and already used as a field type
  at `:197`.

So the seed's native backend fails to resolve (a) an implicit-`self` field and
(b) an imported class name in static-call position, and reports both as
`GlobalLoad: unresolved identifier`. It is a compiler gap, not a source defect;
the sources were deliberately NOT rewritten to appease it.

`SIMPLE_ALLOW_STUB_FALLBACK` was **not** set — the runner offers it and it is
forbidden by the lane rules; emitting empty stubs for a DB daemon's session
constructor and readiness predicate would produce a silently wrong image.

## Consequence

`build/os/fat32-arm64.img` is not produced, so
`build/os/simpleos_arm64_desktop_engine2d.elf` is never reached and
`scripts/check/check-simpleos-arm64-wm-vulkan-pixel-evidence.shs` still returns
`ERROR — nothing was checked` (rc 2).

Blocker 2 of `arm64_wm_vulkan_real_firmware_lane_blocked_2026-09-01.md` — the
AAVMF -> `BOOTAA64.EFI` -> `kernel.elf` `protocol: linux` handover — therefore
remains **UNPROVEN**. No boot was attempted.

## Host prerequisites verified present (so they are not the blocker)

`/usr/share/AAVMF/AAVMF_CODE.fd` + `AAVMF_VARS.fd`, `vendor/limine/BOOTAA64.EFI`
(274432 bytes), `qemu-system-aarch64`, `mkfs.vfat`, and a real host Vulkan
(`NVIDIA TITAN RTX`, `apiVersion 1.4.312`, `driverName NVIDIA`).
The gate's own `--selftest` is green with the fresh seed:
`PASS — 25 selftest fixture(s) checked, ... renderer=n/a`.
