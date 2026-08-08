# Native Library Binding Survey

**Date:** 2026-08-05 · **Lane:** read-only survey (no conversions performed) ·
**Consumer:** the dynamic-loader lane.

**Goal behind it:** a missing native library must degrade to an honest runtime
`unavailable`, not to a link failure and not to a fake success. This survey
sorts every native dependency by *how far it is from the ROCm dlopen pattern*,
because two in-tree precedents already show how to make a library dynamic.

Scope is owned code only. Excluded per `CLAUDE.md` § Owned-Code Scope:
`src/compiler_rust/vendor/**`, `src/runtime/vendor/**`, and the three
header-only vendored libs `src/runtime/{miniaudio,stb_image,stb_truetype}.h`
(discussed as context, never counted as owned).

---

## 0. Executive summary

- **34 distinct owned native libraries** bound (post-filter; see § 6 for the
  census method and its measured 25% pre-filter false-positive rate).
- **7 are already dynamically loaded.** The facility exists and works:
  `spl_dlopen`/`spl_dlsym`/`spl_dlclose` in `src/runtime/runtime_dynload.c`.
- **5 symbol families have NO native definition at all** — C, Rust, or
  otherwise. They exist only as Rust-interpreter match arms that return
  plausible values. **169 symbols total.** These are already lying about their
  capability, and a compiled build would not link them.
- **SDL2 is the single highest-value link-bound conversion**: it is hard-linked
  (`-lSDL2`, direct `SDL_Init`) while its **SDL3 sibling in the same directory
  is already fully dlopen'd**. The pattern to copy is 100 lines away.
- **One confirmed defect** (reported, not fixed): `spl_dlopen`/`spl_dlsym`/
  `spl_dlclose` are each defined **twice**, and the two definitions **decode
  their string argument with different, incompatible value encodings**. See § 5.

---

## 1. Tier A — families with NO native definition (highest conversion value)

These are the ones already lying. Each has `nativeC=0` **and** `nativeRust=0`
across all owned trees, and exists only as interpreter match arms. Under the
interpreter they return plausible non-zero handles while doing nothing; under a
compiled build they would fail to link.

| Family | Symbols | Native def? | Bound how | Underlying library | Optional? | Difficulty |
|---|---|---|---|---|---|---|
| `rt_cranelift_*` | 77 | **None** | interpreter arms only | Cranelift JIT (Rust crate) | Optional — JIT backend | High: 77 syms, hot path (codegen). Needs a real backend, not a loader. |
| `rt_rapier2d_*` | 51 | **None** | interpreter arms only | Rapier2D physics (Rust crate) | Optional — physics | High: 51 syms, hot path (per-frame step). Resolve-once mandatory. |
| `rt_wgpu_3d_*` | 18 | **None** | interpreter arms only | wgpu (Rust crate) | Optional — 3D renderer | Medium: 18 syms, hot path (per-frame). |
| `rt_winit_buffer_*` | 13 | **None** | interpreter arms only | software framebuffer atop winit | Optional — GUI | **Low — best first target.** 13 syms, cold-ish, and the sibling `spl_winit` cdylib already dlopen's cleanly. |
| `rt_renderdoc_*` | 10 | **None** | interpreter arms only | RenderDoc capture API | Optional — debug tooling | Low: 10 syms, cold path, genuinely optional. Ideal dlopen candidate. |

**`rt_winit_buffer_*` — the confirmed instance, fully characterised.**
The `spl_winit` cdylib at `src/runtime/spl_winit/src/lib.rs` exports 34
`rt_winit_*` symbols via `#[no_mangle]`. **Zero of them are `rt_winit_buffer_*`**
(`grep -c 'rt_winit_buffer' lib.rs` → `0`). The only implementation is
`src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_buffer.rs`,
where `rt_winit_buffer_create` returns a buffer id and `rt_winit_buffer_present`
returns `true` — opening no window. Dispatch is routed by prefix at
`winit_sffi/mod.rs:403`. Caller: `src/app/wm_compare/backend_parity.spl:13`,
which documents the family as "performs on the host" — a claim the code does not
meet.

Across the whole `rt_winit_*` surface: **111 symbols routed by the interpreter,
34 implemented in the cdylib → 77 with no native definition.** The gap is not
"partial coverage"; `rt_winit_buffer_*` is absent in full, and it is the
drawing half of the API.

**Method note (fails safe):** the native-definition set was built with a pattern
that matches *calls* as well as definitions, so it is over-inclusive. Anything
this survey calls "no native definition" is therefore a **lower bound** — the
real gap can only be larger. `rt_vulkan_*` was caught by exactly this check and
is *not* listed here (see § 4).

---

## 2. Tier B — already dynamically loaded (the reference patterns)

| Library | Soname candidates | Bound how | Optional? |
|---|---|---|---|
| **ROCm / HIP** | `libamdhip64.so.6` → `.so.5` → `.so`; `libhiprtc.so.6` → `.so.5` → `.so` | `runtime_rocm.c:85` candidate loop + `dlsym` binding macro at `:92`/`:97` — **canonical shape** | Optional |
| **GLFW** | `libglfw.so.3` → `libglfw.so`; `libglfw.3.dylib` → `libglfw.dylib`; `glfw3.dll` → `glfw.dll` | `runtime_glfw.c:18-24`, `glfw_open_library` / `glfw_load_symbol`, per-platform | Optional |
| **SDL3** | `libSDL3.so.0` → `libSDL3.so`; `libSDL3.0.dylib` → `libSDL3.dylib`; `SDL3.dll` | `runtime_sdl3.c:18` (`dlopen(RTLD_NOW\|RTLD_LOCAL)`), candidates at `:135-139` | Optional |
| **spl_winit cdylib** | `build/sffi/libspl_winit.{so,dylib,dll}` | `gui_renderer.spl:96-98` via `spl_dlopen` + **export presence check**; honest failure text at `:136`/`:144` | Optional |
| **CUDA driver (audio)** | `libcuda.so.1` → `libcuda.so` | `sffi/simple_audio_cuda_driver.c:79-80` | Optional |
| **LLVM** | `libLLVM-19.so.1`/`-18`/`-17` → `libLLVM.so`; `.dylib`; `LLVM-C.dll`/`LLVM.dll` | soname candidate table present in tree | Optional (codegen backend) |
| **bcrypt.dll** (Win32) | `bcrypt.dll` | `runtime.c:2023`, `runtime_process.c:542` | Mandatory-ish on Win32 (RNG) |

`gui_renderer.spl` is the **best in-tree model for the campaign's actual goal**:
it dlopens, then verifies the `rt_winit_*` exports are present, then prints a
specific, actionable unavailability message. That is honest degradation. Copy
this, not just the ROCm loader loop.

---

## 3. Tier C — link-bound and optional (convert these)

| Library | Soname candidates | Bound how today | Native def? | Optional? | Difficulty |
|---|---|---|---|---|---|
| **SDL2** | `libSDL2-2.0.so.0` → `libSDL2.so`; `libSDL2-2.0.0.dylib`; `SDL2.dll` | **Hard link**: `-lSDL2` (×9 in build files) + direct `SDL_Init` at `runtime_sdl2.c:56`, `SDL_InitSubSystem` `:88` | Real (`runtime_sdl2.c`) | **Optional at runtime, mandatory at link** | **Low–medium — top target.** SDL3 sibling in the same dir is already converted; symbol set is modest and init is cold-path. |
| **OpenCL** | `libOpenCL.so.1` → `libOpenCL.so`; `OpenCL.dll` | `-lOpenCL` in `scripts/check/check-opencl-generated-2d-readback.shs` | Partial | Optional | Low. **Host proves the need — see § 7.** |
| **CUDA / cuBLAS** | `libcuda.so.1`, `libcublas.so.12` | `-lcuda`, `-lcublas` in check scripts; `scilib/cublas_shim.c` | Real (scilib shims) | Optional | Medium. Audio driver already dlopens `libcuda`; unify on that. |
| **libtorch** | `libtorch.so`, `libtorch_cpu.so`, `libtorch_cuda.so`, `libc10.so` | `-ltorch -ltorch_cpu -ltorch_cuda -lc10` | `torch_sffi.cpp` | Optional (ML) | Medium: C++ ABI makes `dlsym` awkward; needs a C shim. |
| **SQLite3** | `libsqlite3.so.0` | `-lsqlite3` (×4), `runtime_sqlite.c` | Real | Optional | Low: stable C ABI, cold path. |
| **OpenSSL** | `libssl.so.3`, `libcrypto.so.3` | `-lssl` via `pkg-config`, `runtime_https_openssl_core.c` | Real | Optional (HTTPS) | Medium: large surface, version-sensitive soname. |
| **ncurses / tinfo** | `libncurses.so.6`, `libtinfo.so.6` | `-lncurses`, `-ltinfo` | — | Optional (TUI) | Low. |
| **libffi** | `libffi.so.8` | `-lffi` | — | Optional (SFFI) | Low, but it *is* the dynamic-call primitive — bootstrapping concern. |
| **zlib / zstd / libxml2** | `libz.so.1`, `libzstd.so.1`, `libxml2.so.2` | `-lz`, `-lzstd`, `-lxml2` | — | Optional | Low. |
| **tree-sitter** | `libtree-sitter.so.0` | `-ltree-sitter` | — | Optional (parser) | Low. |
| **RenderDoc** | `librenderdoc.so` | `-lrenderdoc` **and** a 0-definition symbol family (§ 1) | **None** | Optional | Low — belongs in Tier A too. |

### Windows system libraries (link-bound, platform-mandatory)
`user32`, `gdi32`, `ws2_32`, `winmm`, `shell32`, `ole32`, `oleaut32`, `propsys`,
`runtimeobject`, `imm32`, `dwmapi`, `uxtheme`, `shlwapi`, `secur32`, `userenv`,
`dbghelp`, `synchronization`, `iphlpapi`, `advapi32`, `kernel32`, `ntdll`.
**D3D/DXGI:** `-ld3d11`, `-ldxgi` (`runtime_directx_core.c`) — these two *are*
reasonable dlopen candidates (optional GPU backend); the rest are not.

### macOS
`-lSystem`, `-lEndpointSecurity`, Cocoa/Metal via `hosted_cocoa.c` (compiled as
Objective-C at `build.rs:162`, linked `static=runtime_sffi_objc` at `:164`).
**Metal has no separate soname to dlopen** — it is a framework; conversion means
weak-linking, not `dlopen`. Not a `dlopen` candidate.

---

## 4. Tier D — mandatory (poor dynamic-loading candidates)

The runtime cannot start without these; do **not** convert.

`libc` (`-lc`), `libm` (`-lm`), `libdl` (`-ldl`), `libpthread` (`-lpthread`),
`librt` (`-lrt`), `libutil` (`-lutil`), `libgcc`/`libgcc_s`, `libunwind`,
`libstdc++`/`libc++`. Confirmed in `build.rs:183` (`dylib=m`), `:186-187`
(`user32`, `gdi32`), `:192` (`util`).

**`rt_vulkan_*` — explicitly NOT Tier A.** The family rollup initially grouped
17 `rt_vulkan_cmd_*` symbols as undefined, but a targeted check found
`nativeC=2`, `nativeRust=11`, and 18 `.spl` callers. Vulkan has a real
implementation; only a `_cmd_` subset is unresolved. Calling the family
stub-only would have been an overclaim. Vulkan is loaded via the ICD loader
(`libvulkan.so.1`), which is itself already a dynamic-dispatch layer.

---

## 5. Defect found (reported, NOT fixed)

**`spl_dlopen` / `spl_dlsym` / `spl_dlclose` are each defined twice, with
incompatible string decoding.**

| | `src/runtime/runtime_dynload.c` | `src/runtime/runtime_native.c` |
|---|---|---|
| `spl_dlopen` | `:14` | `:5685` |
| `spl_dlsym` | `:24` | `:5697` |
| `spl_dlclose` | `:34` | `:5709` |
| dlopen flags | `RTLD_NOW \| RTLD_LOCAL` | `RTLD_NOW` |
| **string decode** | **`rt_interp_cstr(path_value)`** | **`rt_core_string_to_cstring(path_value)`** |

Declared once in `runtime.h:761-762`.

**The flag difference is the lesser problem.** glibc defaults to `RTLD_LOCAL`
when neither flag is given, so `RTLD_NOW` alone is *usually* equivalent — though
not guaranteed by POSIX, and it is exactly the sort of divergence that surfaces
as an interpreter-vs-compiled heisenbug.

**The string-decoding difference is the real defect.** The two functions decode
their argument from **two different value representations** — the interpreter's
tagged value versus `RtCoreString`. If the wrong definition wins for a given
build, the path argument is decoded from the wrong encoding, yielding a garbage
pointer or `NULL` — i.e. a silent `dlopen` failure indistinguishable from a
genuinely missing library. That failure mode directly defeats this campaign's
goal of honest unavailability reporting.

**Which one wins:** the link is performed with `-z muldefs`
(`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:1225`,
`:2241`, `:2249`), which makes duplicate strong symbols **silent instead of
fatal**; first definition encountered wins. The candidate order at
`src/compiler/70.backend/backend/llvm_native_link.spl:1398` lists
`runtime_native` **before** `runtime_dynload`, so **`runtime_native.c`'s
definition is expected to win** — the `RTLD_NOW` / `rt_core_string_to_cstring`
variant. *This ordering inference is not empirically confirmed* (no link was
performed in this lane); confirm with `nm` on a built bundle before acting.

**Already tracked but not analysed:** all three symbols are listed in
`scripts/check/runtime_bundle_duplicate_symbols_baseline.txt:74-76` as expected
duplicates. The baseline records *that* they collide; nothing records that the
two bodies decode their arguments incompatibly. The baseline is therefore
green on a real bug.

**A third resolution mechanism exists:** `runtime_native.c:196` and
`scilib/cublas_shim.c:56,62` resolve via `dlsym(RTLD_DEFAULT, ...)` — process-
global lookup rather than a handle. Three mechanisms for one job.

---

## 6. Census method and measured false-positive rate

Tooling: `/usr/bin/grep` pinned throughout (`ugrep` is the default `grep` here
and would have changed the semantics).

**Unanchored `-l` census: ~95% false-positive.** A naive
`grep -oE '\-l[A-Za-z0-9_.+-]+'` returned `-level` (657), `-linux-gnu` (297),
`-line` (143), `-lower` (107) as the top hits — ordinary English and target
triples. Reported here because it is the exact trap the brief warns about.

**Anchored census**, requiring the token be preceded by start/whitespace/quote
and followed by end/whitespace/quote/comma, over
`--include={*.shs,*.spl,*.rs,*.toml,*.cmake,*.c,*.h,Makefile}` scoped to
`scripts/`, `src/runtime/`, `src/compiler/`, `src/lib/`, and the four
`build.rs`: **84 distinct tokens**.

**Hand-verified sample: 20 distinct tokens (every 3rd, deterministic).**

- True positives (15): `-lbcrypt`, `-lc10`, `-lcuda`, `-ldbghelp`, `-ldxgi`,
  `-lffi`, `-lgcc`, `-limm32`, `-lmingw32`, `-lntdll`, `-lole32`, `-lOpenCL`,
  `-lpthread`, `-lruntimeobject`, `-lshell32`
- False positives (5): `-la` (`ls -la`), `-lh` (`ls -lh`), `-len+1` (C
  arithmetic), `-list-avds` (emulator flag), `-ln`

### **Measured false-positive rate: 5/20 = 25%** (anchored, distinct-token level)

The 34-library figure in § 0 is the **post-hand-filter** count, not the raw 84.
A second census over soname string literals (`"lib*.so*"`, `"*.dll"`,
`"*.dylib"`, `"*.framework"`) returned **69 distinct sonames** and was spot-clean
— string literals are a far higher-precision signal than `-l` flags, and the
loader lane should prefer them.

---

## 7. Host ground truth (verified this session, not assumed)

Verified via `ldconfig -p` and the environment:

| Claim | Verdict | Evidence |
|---|---|---|
| Vulkan works | **Confirmed present** | `/lib/x86_64-linux-gnu/libvulkan.so.1` |
| CUDA works | **Confirmed present** | `/lib/x86_64-linux-gnu/libcuda.so.1` |
| OpenCL context creation fails | **Library present, so the failure is real** | `libOpenCL.so.1` resolves to `/usr/local/cuda/targets/x86_64-linux/lib/` — a **CUDA-bundled ICD**, not a system one. `platform=1 context=0` is consistent with an ICD that enumerates a platform but cannot create a context headless. |
| Metal unavailable (Linux) | **Confirmed** | No Metal on Linux; `hosted_cocoa.c` is macOS-only |
| `DISPLAY` / `WAYLAND_DISPLAY` unset | **Confirmed both unset** | Any windowing path must degrade honestly *right now* on this host |

Also measured: `libSDL2-2.0.so.0` **present**; `libSDL3.so.0` **ABSENT**;
`libglfw.so.3` **ABSENT**; `libX11.so.6`, `libwayland-client.so.0`,
`libasound.so.2`, `libpulse.so.0`, `libfreetype.so.6`, `libfontconfig.so.1`,
`libsqlite3.so.0`, `libssl.so.3` all present; `libamdhip64.so` resolves to
`.so.5` (ROCm's candidate loop tries `.so.6` first, then `.so.5` — correct).

**Note the asymmetry this host exposes:** SDL3 and GLFW are *absent* and are
*already dlopen'd*, so they degrade cleanly. SDL2 is *present* and *hard-linked*
— so the link-bound path happens to work here and its brittleness is invisible
on this machine. Do not treat "SDL2 works" as evidence it is safe.

**freetype/fontconfig:** present on the host, but `grep` found **no owned
reference** to either in `src/runtime` — font handling goes through
`runtime_font.c` and the vendored `stb_truetype.h`. Not a dependency.

**X11/Wayland:** no direct owned binding found (`wayland` → 0 owned files; `x11`
hits are only in vendored headers and an unrelated `runtime_directx_core.c`
match). Access is indirect, via SDL/GLFW/winit. Converting those three covers
the display stack.

---

## 8. What this survey cannot see

1. **No build was performed, and no binary was inspected.** Every claim about
   *which* duplicate definition wins, and about what actually ends up in a
   linked artifact, is inferred from source ordering. `nm`/`readelf` on a real
   bundle is the only authority. § 5's "runtime_native.c wins" is **unconfirmed**.
2. **Runtime-constructed library names are invisible to a string-literal
   census.** A soname assembled by concatenation, read from an env var, or
   built from a version number will not appear in the 69-soname list.
3. **Transitive dependencies are out of scope.** SDL2 pulls X11, ALSA, pulse,
   and more; dlopening SDL2 does not make those honest — it moves the failure.
4. **The vendored header-only libs hide their own `dlopen` calls.** `miniaudio.h`
   dlopens `libasound.so.2`, `libpulse.so.0`, `libjack.so.0`, `libsndio.so`,
   `libOpenSLES.so`, `libaaudio.so`, `dsound.dll`, `avrt.dll`, `mmdevapi.dll`,
   `winmm.dll` internally. Correctly excluded from owned counts, but the loader
   lane inherits their failure modes and cannot control them.
5. **"No native definition" is a lower bound, not an exact set.** The
   definition-side pattern also matches call sites, so the set is
   over-inclusive and the derived gap under-inclusive. The true Tier A is ≥ 169
   symbols. `rt_vulkan_*` demonstrates the check working as intended.
6. **Interpreter arms were counted from string literals** in
   `interpreter_extern/`. An arm dispatched by computed name or by prefix match
   (as `winit_sffi/mod.rs:403` does) is undercounted.
7. **Nothing here measures whether a stub is *reached*.** A family with no
   native definition may be dead code. This survey establishes the capability
   lie, not its blast radius. `rt_cranelift_*` (77 symbols) especially warrants
   a reachability pass before anyone invests in it.
8. **Windows and macOS were not exercised.** All host verification is Linux
   x86_64. Win32 and Darwin binding claims are source-only.
9. **Worktrees under `.claude/worktrees/**` were excluded**; they contain
   parallel-lane copies of the same `build.rs` files and would have inflated
   every count roughly 6×.

---

## 9. Recommended conversion order

1. **`rt_winit_buffer_*`** (13 syms) — lying today, and the honest-degradation
   model (`gui_renderer.spl`) is already in place next to it.
2. **SDL2** — link-bound, and the already-converted SDL3 sibling sits in the
   same directory.
3. **`rt_renderdoc_*`** (10 syms) — small, cold, genuinely optional, currently
   both link-bound *and* undefined.
4. **OpenCL** — link-bound, and demonstrably broken on this very host.
5. **D3D11 / DXGI** — optional GPU backend, currently link-bound.
6. **SQLite3, zlib, zstd, libxml2, tree-sitter, ncurses** — low-risk, stable C
   ABIs, cold paths.
7. **OpenSSL, libtorch** — larger surfaces; libtorch needs a C shim first.
8. **`rt_wgpu_3d_*`, `rt_rapier2d_*`, `rt_cranelift_*`** — these need a real
   backend implementation, not a loader. Do not let "convert to dlopen" disguise
   "this was never written."
9. **Never:** libc, libm, libdl, libpthread, libgcc, libstdc++, Metal/Cocoa.

**Before any of the above:** resolve the § 5 duplicate-definition defect. Every
conversion in this list routes through `spl_dlopen`, and two incompatible
implementations of it are a foundation that will produce silent failures in
precisely the code meant to make failures loud.
