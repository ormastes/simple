# SIMPLE_JIT_STRICT cannot resolve `use os.*` imports (src/os not a module root)

Status: open (diagnosed, not fixed). Class: (c) seed defect. Lane `xraychk`, Windows seed-tip, 2026-11-14.

`test/01_unit/lib/nogc_sync_mut/trace/xray_native_inprocess_patch_spec.spl` imports
`os.sosix.host.code_patch_adapter` (exists at `src/os/sosix/host/code_patch_adapter.spl`). The spec has native
externs, so the runner uses JIT strict and fails: `cannot resolve import ... module path segment 'os' not found`;
result `no examples executed (zero-examples)`. Interpreter mode resolves `os.` fine (other `use os.*` specs execute).
The spec is aarch64-Linux-only by design (it is meant to record why and assert nothing on other hosts), but the
import failure prevents even that. Fix: add `src/os` as a module root in the seed JIT resolver.
