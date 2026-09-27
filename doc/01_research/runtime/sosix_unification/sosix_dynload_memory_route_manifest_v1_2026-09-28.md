# SOSIX route manifest v1: dynamic libraries and executable memory

Status: **partial RU-001 census**, inspected at `1cc5b43c07c` on 2026-09-28.
The rows classify current routes; they do not claim SOSIX loader admission,
cross-engine parity, or a SimpleOS release.

## Route keys

| Key | Profile | Current effect owner |
|---|---|---|
| S | Hosted Simple SFFI consumer | `std.sffi.dynamic` and raw runtime loader ABI |
| P | Compiler block plugin | `compiler.blocks.plugin_startup` and raw runtime loader ABI |
| W | Compiler WFFI compatibility | `compiler.core.wsffi` and raw runtime loader ABI |
| M | Hosted SMF/JIT mapping | `compiler.loader.smf_mmap_native` and runtime VM externs |
| H | Hosted mapping provider | `os.hosted.dedicated_host_posix` and runtime VM externs |
| X | SOSIX host library plan | Pure callback contract; no installed loader provider |
| I | Rust bootstrap interpreter | Hand-maintained `interpreter_extern` registration |

## Classified symbols and migration disposition

Signatures are Simple declarations unless stated otherwise. Callers are verified
direct callers, not a claim that every transitive consumer has been found.

| Symbol and source | Category; signature; caller → owner → route | Disposition and evidence gap |
|---|---|---|
| `spl_dlopen_checked`, `spl_dlsym_checked`, `spl_dlclose` in [`dynamic.spl`](../../../../src/lib/nogc_sync_mut/sffi/dynamic.spl) | Dynamic library admission, symbol resolution, and release; `(text,*mut i64)->i64`, `(i64,text,*mut i64)->i64`, `(i64)->i64`; `DynLib`, `DynLoader`, and exact-artifact constructors → SFFI owner → S | Raw handles and function pointers remain exposed through unsafe APIs. A checked status does not prove artifact, ABI, generation, or callable lifetime. |
| `DynLib.load_checked`, `DynLib.sym_checked`, `DynLib.close`, same source | Legacy library lifecycle; `(text)->Result<DynLib,text>`, `(text)->Result<i64,text>`, `()->()`; singleton and direct callers → copyable `DynLib` → S | `close` zeros one handle copy. Resolved `DynI64FnSlot` stores a raw pointer and path, so stale copies can invoke an unloaded mapping. Keep this route compatibility-only until an owner retains mapping/pin through call retirement. |
| `ExactArtifactDynLib.load_exact_linux`, same source | Linux sealed-snapshot admission; `(text,text)->Result<ExactArtifactDynLib,text>`; signed and unsigned exact-artifact callers → `/proc/self/fd` hash and checked load → S | Exact bytes are checked on Linux, but the unsigned constructor accepts caller-supplied expected hash. The signed constructor adds trust verification. No Darwin/FreeBSD/Windows equivalent or SOSIX capability owner is established. |
| `wffi_load`, `wffi_get`, `wffi_close` in [`wsffi/mod.spl`](../../../../src/compiler/10.frontend/core/wsffi/mod.spl) | Compiler WFFI compatibility; `(text)->i64`, `(i64,text)->i64`, `(i64)->i64`; WFFI users → direct `spl_*` externs → W | Fail-closed panic on checked load/lookup, but raw handle and pointer ownership is separate from `std.sffi.dynamic`. Preserve legacy ABI while routing new admissions through one owner. |
| `activate_plugin` in [`plugin_startup.spl`](../../../../src/compiler/15.blocks/plugin_startup.spl) | Lazy block plugin activation; `(text)->bool`; compiler startup indexes manifests, activation directly loads and resolves `.so` symbols → P | The index phase avoids `dlopen`, but activation uses its own raw handle and caches `_SoBlockProxy` function pointers with no SOSIX generation pin. A loader cutover must keep cold startup lazy and prevent unload while proxies are callable. |
| `FontRasterizer.load` route in [`spl_fonts.spl`](../../../../src/lib/nogc_sync_mut/sffi/spl_fonts.spl) | Font-provider load and symbol resolution; checked `(text,*mut i64)->i64` `spl_dlopen_checked` and `(i64,text,*mut i64)->i64` `spl_dlsym_checked`; font renderer → dedicated SFFI facade → S | This facade deliberately bypasses `DynLib` because of a documented interpreter method-lookup defect. Keep its copied glyph bytes and provider lifetime intact during unification; a new shared wrapper alone does not qualify the seed route. |
| `_bulk_ensure_loaded` in [`backend_metal.spl`](../../../../src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl) | Lazy GPU transfer cdylib load; `()->bool`; Metal paint path → process-global handle and three cached function pointers → raw checked loader ABI → S | Failed symbol lookup closes the handle. A successful handle is retained process-wide; no SOSIX library capability or generation pin protects cached pointers. Preserve the no-load cold path and explicit backend qualification. |
| `steam_sffi_find_bridge_path`, `steam_sffi_probe_bridge` in [`sffi_backend.spl`](../../../../src/os/game/steam/sffi_backend.spl) | Game bridge discovery and raw `spl_dlopen`/`spl_dlsym`; `()->text` plus `(text,bool,[text])->SteamSffiBackendStatus`; Steam backend → environment/path scan and direct loader externs → S | This is a separate raw-handle route that probes required symbols and mock/real readiness. The result is a capability report, not artifact authentication or shared loader lifetime. |
| `spl_dlopen*`, `spl_dlsym*`, `spl_dlclose` in [`runtime_native.c`](../../../../src/runtime/runtime_native.c) and [`wsffi.rs`](../../../../src/compiler_rust/compiler/src/interpreter_extern/wsffi.rs) | Hosted native and bootstrap interpreter implementations; native C checked status/out ABI; seed `(&[Value])->Result<Value,CompileError>` registered in `interpreter_extern/mod.rs` → S/P/W or I | The seed registry includes these names; the `dynamic.spl` header saying `spl_dlopen` is not whitelisted is stale. Error and out-parameter parity require source-matched differential tests. Seed behavior is bootstrap evidence only. |
| `native_mmap_file`, `native_make_executable`, `native_make_rw`, `native_munmap` in [`smf_mmap_native.spl`](../../../../src/compiler/99.loader/smf_mmap_native.spl) | File/executable mapping; `(text,i64,i64,i64,i64)->[i64]`, `(i64,i64)->bool`, `(i64,i64)->bool`, `(i64,i64)->bool`; SMF/JIT loader → direct `rt_open_fd`/`rt_mmap_raw`/`rt_mprotect`/`rt_munmap_raw` → M | `loader/smf_mmap_native.spl` is a compatibility adapter over this owner. Preserve mapping extent, W^X transitions, failure sentinels, in-flight calls, and retirement during SOSIX VM migration. |
| `pack_window_map`, `pack_read_range` in [`aspect_pack_io.spl`](../../../../src/compiler/99.loader/aspect_pack_io.spl) | Cold aspect-pack range I/O; `(text,i64,i64)->PackWindow` and byte-range read; aspect-pack loader → `rt_io_file_*` primary read plus aligned `rt_mmap_raw` window → M | This is deliberately partial-range I/O, separate from whole-file SMF mapping. Keep the 64 MiB declaration cap, 64 KiB alignment, map extent, and interpreter-compatible byte route in any SOSIX file/VM migration. |
| `PosixDedicatedHost.mmap`, `.mprotect`, `.munmap` in [`dedicated_host_posix.spl`](../../../../src/os/hosted/dedicated_host_posix.spl) | Hosted mapping provider; `(HostMapRequest)->HostMappedRegion`, `(HostMappedRegion,i64)->bool`, `(HostMappedRegion)->bool`; dedicated-host consumers → raw runtime VM externs → H | This provider validates requests and translates anonymous-map flags for macOS/FreeBSD; the SMF/JIT owner above does not call it. A common service boundary must retain platform flag conversion and mapping authority without creating an eager loader dependency. |
| `sosix_host_library_plan`, `sosix_host_library_dispatch` in [`library_capability_adapter.spl`](../../../../src/os/sosix/host/library_capability_adapter.spl) | Pure host-library plan/callback; `(SosixHostLibrarySnapshot)->SosixHostLibraryPlan`, `(SosixHostLibraryPlan,fn(SosixCapabilityRef,text,text)->bool)->bool`; currently unit tests only → X | The plan checks capability shape, name, and ABI text, then invokes a supplied callback. No production caller or loader provider binds the capability to a mapped generation; this is not the S/P/W effect route. |

## Consequences for RU-042 and generated dynload

1. The current product path has multiple dynamic-library entry points:
   `std.sffi.dynamic`, compiler WFFI/plugin activation, fonts, Metal transfer,
   and Steam. SMF/JIT executable memory and cold aspect-pack range I/O have
   separate owners. The SOSIX host-library adapter is currently a pure plan,
   so routing it into a consumer without a live provider would add another
   unqualified route.
2. The first effectful loader bridge must bind an authenticated artifact and
   ABI to one live generation, retain that generation across symbol invocation,
   and reject calls after revocation. A raw `i64` function pointer or a checked
   `dlopen` status cannot establish those facts.
3. A single hosted mapping provider can be considered only after the loader's
   W^X, extent, platform flags, lazy startup, and in-flight retirement behavior
   is preserved. The existing `PosixDedicatedHost` conversion is direct evidence
   that raw Linux `MAP_ANONYMOUS` values are not portable as-is.
4. RU-001 remains open for the remaining service declarations, interpreter
   externs, loader imports, GPU/library consumers, and provider call graphs.
