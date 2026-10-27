# Backend Dynamic Plugins as Build Groups + Stdlib Static Archive

**Status:** plan, 2026-10-27. **Branch:** `work/backend-dylib-plan` (from `release/1.0.0`).
**Directive:** every backend except the host backend is a dynamic library loaded at
runtime, each built as its own build group; bootstrap default = host backend only,
no slowdown, no effect on a running phase-3/stage3. Toolchain clang+lld only
(Windows: llvm-mingw UCRT). No `Any` outside `unsafe`, no inheritance, generics `<>`.

## 1. Verified starting point (file:line, this worktree)

| Fact | Where |
|---|---|
| v1 ABI: entry `"simple_backend_plugin_v1"`, `simple_backend_descriptor_v1` {identity, version, build_id, mir_abi_digest, roles, caps, targets_wire, vtable}, 6-fn vtable | `src/compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h:10,53-69` |
| Loader done: stage copy + sha256 + `load_checked` lease | `backend_plugin/dynamic_loader.spl:58,71,75,134` |
| `load_backend` branches on `has_plugin_path` → `load_dynamic_backend_v1` → `DynamicBackendAdapter` | `backend_plugin/loader.spl:40-93` (`:76`) |
| Descriptor is a **local projection** "until descriptor metadata is returned in v2" | `loader.spl:53-64` |
| C bridge (LoadLibraryW/dlopen, boxed `[u8]` wire) | `src/runtime/runtime_backend_plugin.c:23,27` |
| **No provider exports the symbol; only callers of `load_backend(` are `loader.spl` and `session_authority_v2.spl`** — nothing production passes `plugin_path` | grep, `backend_plugin/*.spl` |
| Static link: 12 ports (llvm-lib, c, wasm, native, hip, opencl, vulkan, lean, byl, vhdl, irtc, lua) | `src/plugins/backend_registry/full_static_backend_ports.spl:6-17,29-70` |
| CUDA already has the "emptied table" pattern: `selected_cuda_backend_table_v1() -> []`, mode `"dynamic"` | `src/compositions/cuda_dynamic/plugins/backend_registry/selected_cuda_backend.spl` (vs static `src/plugins/backend_registry/selected_cuda_backend.spl:9-13`) |
| Bootstrap selects composition root from `src/compiler/simple.sdn:5-8 compiler_backends.cuda.placement`; K1 policy roots `kernel_llvm{,_cranelift}` | `scripts/bootstrap/bootstrap-from-scratch.sh:861,1755-1772,1856-1862`; `scripts/bootstrap/lib/managed-cuda-selection.shs:1-25` |
| Build config entry: `targets.sdn` (root; `build.sdn` wins if present), kinds `binary|library|shared|test`, **no include/group directive** (parser handles `target` blocks only) | `src/app/build/targets/build_targets.spl:73-77,291`; `targets_cli.spl:72-80` |
| Executor maps `library`→`--emit-archive` (`.a`), `shared`→`--emit-shared`; a `shared` target already exists (`//provider:provider_cli_native`) | `target_executor.spl:82,106-121`; `targets.sdn:17-20`; `native_build_main.spl:285-286` |
| GPU **runtime** provider slots (`SIMPLE_{CUDA,VULKAN,METAL}_PROVIDER_PATH` + `_SHA256`) live in `runtime_dynload.c`, not `runtime_native.c:2722` (that line is `SIMPLE_GUI_HTML_PROVIDER_PATH`) | `src/runtime/runtime_dynload.c:84-95`; `doc/05_design/gpu_dynamic_backend_provider.md` |
| No stdlib archive, no cpu-tier axis anywhere under `src/app/build`, `src/app/cli`, `scripts/build` | grep (0 hits) |

## 2. Design

### 2.1 Provider entry shim + descriptor v2
- One shared C boundary file `backend_plugin/abi/provider_entry_v1.c` (compiled into every
  provider dylib) owns the static `simple_backend_descriptor_v1` + vtable and forwards the six
  vtable calls to six `--no-mangle` Simple functions `spl_provider_{open_session,compile_module,
  finalize_object,diagnostics,close_session,release_buffer}_v1`. Its Simple twin
  `backend_plugin/provider_shim.spl` implements them generically over `BackendPortV1`
  (`backend_port.spl:69`): `provider_shim_bind<P>(port: BackendPortV1, identity: text, targets: [text])`.
- Per backend: `src/plugins/backend_<name>/provider_entry.spl` (≈10 lines: bind the existing
  `<name>_backend_port_v1()`; the `_desc` capability list becomes `capabilities`).
- **Descriptor v2 = wire, not a new struct.** Add to `runtime_backend_plugin.c` a
  `spl_backend_plugin_descriptor_v1(handle) -> [u8]` that serialises the *foreign* descriptor
  (SBP1 envelope); `loader.spl:53-64` decodes it into `BackendPluginDescriptorV1` and the local
  projection is deleted. Admission (`admission.spl:12`) then checks provider `mir_abi_digest`
  and `targets_wire` against the request — closing the "until v2" gap without bumping the C ABI.

### 2.2 Build groups via Simple's build config (targets.sdn)
- Add two parser directives to `build_targets.spl` (fail-closed, new error codes
  `include-missing`, `include-cycle`, `unknown-group-target`):
  `include config/build/<file>.sdn` (relative to repo root, depth ≤ 2) and
  `group <name>: default: <bool>; targets: <labels>`. `load_targets_file` recurses; labels stay
  one flat namespace so `depends:` keeps working. `targets_cli.spl` gains `target-group <name>`.
- Root `targets.sdn` only *references* sub-configs and declares `group host: default: true` =
  `//compiler:*` (today's binaries). Nothing in `host` depends on a plugin target, so a default
  build/bootstrap never parses a provider's entry closure or links a provider.
- Sub-configs (each is one build group):
  `config/build/backend_plugins.sdn` — one `kind: shared` target per backend
  (`//backend:c`, `//backend:wasm`, `//backend:cuda`, `//backend:vulkan`, `//backend:hip`,
  `//backend:opencl`, `//backend:lua`, `//backend:lean`, `//backend:vhdl`), entry
  `src/plugins/backend_<n>/provider_entry.spl`, output
  `build/backends/<triple>/backend_<n>-<triple>-v1.<dll|so|dylib>`.
  `config/build/backend_llvm_cross/<triple>.sdn` — one `shared` target per LLVM triple
  (`//backend:llvm-<triple>`, entry `src/plugins/backend_llvm_lib/cross/provider_entry_<triple>.spl`,
  `targets_wire=[triple]`, flags from `llvm_cross_target.spl`), each file included from
  `backend_plugins.sdn`.
  `config/build/stdlib_static.sdn` + `scripts/build/build-stdlib-static.shs` — §2.5.
  `config/build/cpu_tiers.sdn` is the sibling SIMD lane's include on the same entry point; its doc
  (`C:/dev/wt-simdtier/.../cpu_tier_multibuild.md`) was absent at planning time, so this plan
  keeps `cpu_tier` a plain string axis (`host` default) in names, sidecars and cache keys only.

### 2.3 Registry: resolve by plugin_path, static tables emptied
- Generalise the CUDA pattern: `src/compositions/backends_dynamic/plugins/backend_registry/
  full_static_backend_ports.spl` exports the **same pub names** with the host port only (table
  `[llvm-lib]`); `selected_cuda_backend.spl` = the existing dynamic overlay. `simple.sdn`
  `compiler_backends:` grows `placement: dynamic` for every non-host backend; bootstrap's
  existing selection code (`bootstrap-from-scratch.sh:1755-1829`) is extended to that one extra
  root and no other script changes. A running stage3 is unaffected: it compiled the snapshot it
  captured (`bootstrap_cuda_source_snapshot_require`).
- Fallback wiring: when `select_static_backend_v1` (`static_backend_registry.spl:161`) misses,
  the driver calls new `backend_plugin/plugin_search.spl::resolve_backend_plugin_path(name,
  triple, host) -> Result<text, PluginSearchError>` and then `load_backend(request with
  plugin_path)`. Search order: `SIMPLE_BACKEND_PLUGIN_PATH` → `<exe_dir>/../lib/simple/backends/<triple>/`
  → `~/.simple/backends/<semver>/<triple>/`. Exact file name only, no globbing.

### 2.4 Version/ABI admission (owned by the sibling lib-versioning lane)
- Artifact names: `backend_<name>-<triple>-v<abi>.<dll|so|dylib>`,
  `libsimple_std-<semver>-<triple>-<tier>.a`. Every artifact ships a sidecar `<artifact>.lib.sdn`
  with `name, semver, abi_major, abi_minor, iface_digest, producer, triple, cpu_tier, sha256`;
  producers (`--emit-shared`/`--emit-archive` via the target executor) emit it.
- Admission is pure Simple in `src/compiler/80.driver/libver/`:
  `fn libver_admit(sidecar_text: text, host: LibHostReq) -> LibAdmit` with an enum refusal
  reason. **Our call sites:** `dynamic_loader.spl:134 load_dynamic_backend_plugin_lease` calls it
  *before* the staged copy/`load_checked`/entry-symbol resolve and compares the staged sha256 to
  `sidecar.sha256`; the stdlib link step (§2.5) calls it at link time. No `--force` bypass.

### 2.5 Stdlib static archive (own build group)
- `config/build/stdlib_static.sdn`: `//std:libsimple_std` `kind: library`, entry
  `src/lib/std_archive_root.spl` (imports the std closure), output
  `build/std/<triple>/<tier>/libsimple_std-<semver>-<triple>-<tier>.a` + sidecar. Built by the
  executor's existing `--emit-archive` path (`target_executor.spl:82,118`); PR verifies it runs
  `llvm-ar` (never `ar`/MSVC `lib`). `scripts/build/build-stdlib-static.shs` is the thin wrapper
  (`bin/simple build target //std:libsimple_std --triple --tier`) used by CI/bootstrap Stage 4.
- Cache key = `iface_digest(src/lib closure)` ⊕ `native_build_cache_scope_key` producer identity
  ⊕ triple ⊕ tier; directory-partitioned like `build/bootstrap/native_cache/<lane>/`.
- Consumer: `native-build --std-archive <path>|auto`. With a libver-admitted archive whose
  `iface_digest` equals the current `src/lib` digest, the driver drops std units from the compile
  set and appends the `.a` to the link; otherwise it compiles std as today and says why.

### 2.6 GPU runtime provider slot: **keep separate, share admission + naming**
`runtime_dynload.c:84-95` is an *execution* ABI (`SimpleGpuProviderAbiV1`: process-wide pinned
slot, consumed by every compiled app at run time, kernel dispatch), while v1 is a *compiler
session* ABI (lease per `BackendSession`, MIR in / object out). Unifying would make every app
runtime depend on the compiler descriptor wire and vice versa, and the GPU slot's `/proc/self/fd`
re-open hardening has no analogue in a compiler lease. Decision: two ABIs, **one** sidecar
format, **one** `libver_admit`, **one** search-path resolver (`plugin_search.spl` reused by a
Simple twin of the env-path lookup). Re-evaluate only if a GPU *codegen* provider ever needs the
runtime handle.

### 2.7 Bootstrap non-interference (hard constraints)
Default group host-only; no `depends:` edge from `//compiler:*` into any new target; new
sub-configs add parse work of a few KB only; no file under `src/plugins/backend_registry/` or
`scripts/bootstrap/` changes before PR7; nothing touches `C:/dev/p3new` or `src/runtime/providers/vector`.

## 3. Specs (modern SSpec, manual-first; see `doc/07_guide/infra/sspec_antipatterns.md`)
Each spec has a user-voice module docstring (Purpose/Operator workflow/Troubleshooting),
`# @manual_section:`, outcome-named `it`, `# @req REQ-BACKEND-DYN-00n`, and `step("...")` lines
(pattern: `test/01_unit/app/arch_check_spec.spl:32-58`).
- **PR1 e2e on `backend_c`** — chosen over wasm: C emits source (`emit-source`, target `*`,
  `full_static_backend_ports.spl:33-35`), so the provider dylib needs only pure-Simple codegen +
  runtime core, and "run the result" is `clang` (already mandatory). WASM would require a wasm32
  object pipeline *and* a wasm runtime to execute (`wasmtime.h` is absent on this host; see the
  C-runtime guard's `scv_wasm_shim.c` SKIP). `test/02_integration/backend_plugin/backend_c_dynamic_provider_spec.spl`:
  build `//backend:c` via the target executor (`--emit-shared`) → `load_backend` with
  `plugin_path` → compile a 3-line program through the session → `clang` the emitted C → run,
  expect exit 0 and stdout `hello`. Red first (no exporter), green after PR1-PR3.
- **Stdlib archive** `test/02_integration/build/stdlib_static_archive_spec.spl`: build
  `//std:libsimple_std`; app `native-build --std-archive auto` links and runs; rebuild shows
  `std units compiled: 0` in `--verbose`; tampered sidecar sha256 → libver refusal named.
- **Config** `test/01_unit/app/build/targets_include_group_spec.spl`: include/group parse,
  missing include, cycle, default group excludes plugin targets.

## 4. Ordered PR list (Haiku-sized; each lands via `work/<topic>` PR; do not batch lint)
Worker rule, verbatim, for every worker: *Kill processes ONLY by a PID you started yourself.
NEVER use taskkill /IM, Stop-Process -Name, or path/command-line matching. NEVER touch any process
whose command line or env contains P3-RUN (SIMPLE_P3_RUN), or anything under C:/dev/p3new.*

| # | Scope | Exact files |
|---|---|---|
| 1 | targets.sdn `include`/`group` directives + CLI `target-group`; unit spec (red→green) | `src/app/build/targets/build_targets.spl`, `targets_cli.spl`, `targets.sdn`, `test/01_unit/app/build/targets_include_group_spec.spl` |
| 2 | Provider shim (C boundary + Simple twin) + `backend_c` entry; `config/build/backend_plugins.sdn` with only `//backend:c` | `backend_plugin/abi/provider_entry_v1.c`, `backend_plugin/provider_shim.spl`, `src/plugins/backend_c/provider_entry.spl`, `config/build/backend_plugins.sdn` |
| 3 | Descriptor v2 wire; delete loader projection; admission checks it; e2e spec goes green | `src/runtime/runtime_backend_plugin.c`, `backend_plugin/loader.spl:53-64`, `admission.spl`, `test/02_integration/backend_plugin/backend_c_dynamic_provider_spec.spl` |
| 4 | Search path + libver call sites (consumes sibling lane's `libver_admit`) + sidecar emission in executor | `backend_plugin/plugin_search.spl`, `dynamic_loader.spl:134`, `src/app/build/targets/target_executor.spl` |
| 5 | Remaining 8 provider entries + targets (one PR per 2-3 backends: wasm/lua/lean; vhdl/opencl/hip; cuda/vulkan) | `src/plugins/backend_<n>/provider_entry.spl`, `config/build/backend_plugins.sdn` |
| 6 | Cross LLVM providers: per-triple sub-configs + entries (start x86_64-linux, aarch64-linux, riscv64-linux) | `config/build/backend_llvm_cross/<triple>.sdn`, `src/plugins/backend_llvm_lib/cross/provider_entry_<triple>.spl` |
| 7 | `backends_dynamic` composition (host-only static table) + `simple.sdn placement: dynamic` + bootstrap root selection; driver fallback to `plugin_search` | `src/compositions/backends_dynamic/plugins/backend_registry/*.spl`, `src/compiler/simple.sdn`, `scripts/bootstrap/bootstrap-from-scratch.sh:1755-1829`, driver caller of `select_static_backend_v1` (locate by grep in `80.driver`) |
| 8 | Stdlib archive group: root module, sub-config, wrapper script, sidecar, `--std-archive` consumer + spec | `src/lib/std_archive_root.spl`, `config/build/stdlib_static.sdn`, `scripts/build/build-stdlib-static.shs`, `src/app/cli/native_build_main.spl`, `native_build_output_plan.spl`, `test/02_integration/build/stdlib_static_archive_spec.spl` |
| 9 | Docs/wiki: update `versioned_codegen_backend_plugin.md`, `backend_layer_artifact_matrix.md`, feature_expert skill | `doc/05_design/*.md`, `doc/00_llm_process/feature_expert/backend_plugin/skill.md` |

Open items to record as todos, not NOTEs: `--emit-archive` archiver identity (must be `llvm-ar`);
whether `--no-mangle` already gives C-ABI symbol export on Windows PE (`__declspec(dllexport)`
is in the C shim, so Simple symbols need only be visible to it); cpu_tiers.sdn alignment once the
SIMD doc lands.
