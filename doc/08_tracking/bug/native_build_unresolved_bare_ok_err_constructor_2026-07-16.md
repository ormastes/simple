---
id: native_build_unresolved_bare_ok_err_constructor_2026-07-16
status: OPEN
severity: high
discovered: 2026-07-16
area: compiler/native-build
related: src/os/drivers/nvme/_NvmeDriver/driver_operations.spl
related: src/os/services/vfs/vfs_boot_init.spl
related: doc/08_tracking/bug/simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md
---

# Native-build: bare `Ok(...)` / `Err(...)` Result constructors are unresolved → cr2=0x0 fault

## Summary

Under the SimpleOS freestanding native-build, a BARE `Result` constructor call
— `Ok(x)` / `Err(x)` (the prelude-alias form) — is not resolved to a real
function in some modules. At runtime the guest prints `[WARN] unresolved fn: Ok`
/ `[WARN] unresolved fn: Err` and then faults with `cr2=0x0` (a call through a
null/unresolved function pointer). The QUALIFIED form `Result.Ok(x)` /
`Result.Err(x)` resolves correctly (the enum-variant constructor), and the same
modules use it successfully in ~200 other places.

## Evidence (live QEMU, 2026-07-16)

SimpleOS WM fullscreen harness, field-fix seed (`4dcca1aa27`) build. Serial:

```
[vfs-init] pure-nvme begin
[vfs-init] pure-nvme grant ok
[WARN] unresolved fn: Ok
[WARN] unresolved fn: Ok
[WARN] unresolved fn: Err
[vfs-init] pure-nvme lease policy degraded nvme-fs-transfer-not-ready:missing-nvme-doorbells
[WARN] unresolved fn: Ok
[fault] rip=0x00000000008c8d42 cr2=0x0000000000000000   # inside NvmeDriver.init_from_grant
...
[fault] rip=0x0000000000...     cr2=0x0                 # inside transfer_evidence_from_reversible_probe
```

ELF symbolization pins the faults inside
`os__drivers__nvme___NvmeDriver__driver_operations__NvmeDriver_dot_init_from_grant`
and `..._dot_transfer_evidence_from_reversible_probe`, both of which return
`Result` via bare `Ok(...)` / `Err(...)`. The faults are RIP+2-recovered
(non-fatal individually) but the boot never reaches framebuffer/desktop-ready —
so no render/PPM. `driver_operations.spl` had 22 bare sites (vs 200 qualified);
`vfs_boot_init.spl` had 65 bare (0 qualified) — exactly the executed pure-nvme
boot path.

## Root cause (hypothesis)

Native-build closure discovery / name resolution does not always bring the
prelude `Ok`/`Err` free-function aliases into a module's resolved symbol set, so
a bare `Ok(...)` call lowers to an unresolved extern that traps at runtime. The
qualified `Result.Ok`/`Result.Err` path goes through the enum-variant
constructor and is always resolved. This is adjacent to the documented
native-build closure-discovery limitations (`.claude/rules/bootstrap.md` §
"Native-Build Closure Discovery").

## Workaround (pure-Simple, applied)

Qualify every bare `Ok(...)`/`Err(...)` → `Result.Ok(...)`/`Result.Err(...)` in
the executed SimpleOS boot path (`driver_operations.spl`, `vfs_boot_init.spl`).
This is the unblock for the SimpleOS WM render; it does NOT fix the underlying
compiler resolution gap.

## Real fix (compiler, not yet done)

Native-build name resolution / closure discovery must resolve the bare
`Ok`/`Err` prelude aliases (or the frontend must desugar bare `Ok`/`Err` to the
`Result.Ok`/`Result.Err` variant constructors before native lowering) so the
compact form never lowers to an unresolved extern. Until then, freestanding/OS
code should prefer the qualified form.
