# SOSIX route manifest v1: compiler, interpreter, and SMF loader

Status: **partial RU-001 census**, source inspected at `0dca7105252` on
2026-09-26. This records selected file, environment, process, and memory
routes. It does not prove a generated dispatch registry, native/interpreter
parity, compiler service injection, or loader cutover. The Rust interpreter
below is the bootstrap seed, not the product's pure-Simple authority.

## Route keys

| Key | Profile | Current effect owner |
|---|---|---|
| D | Hosted compiler driver | Direct Simple `rt_*` externs through native runtime or interpreter dispatch |
| I | Rust bootstrap interpreter | Hand-maintained `interpreter_extern/mod.rs` registry and Rust handlers |
| N | Native hosted executable | C runtime or platform provider implementation |
| L | Hosted SMF/JIT loader | Lazy loader service cells and executable/file mapping adapters |

## Classified symbols and migration disposition

| Symbol and source | Category; signature; caller → owner → route | Disposition and evidence gap |
|---|---|---|
| `rt_file_read_text`, `src/compiler/80.driver/driver_source_loading.spl` | Source-file effect; `(text) -> text`; source collection and entry-closure scanning → driver → D | Preserve source order, empty/unreadable distinction, cache identity, and bootstrap recovery when injecting a SOSIX file service. The driver still calls the raw extern. |
| `rt_file_exists`, `rt_path_absolute`, `rt_dir_list`, `rt_dir_walk`, same file | Path/discovery effects; `(text) -> bool`, `(text) -> text`, `(text) -> [text]`, `(text) -> [text]`; source collection → driver → D | Current false/empty sentinels conflate absence, denial, and provider failure. Migration needs typed reasons without changing legacy compilation results. |
| `rt_env_get`, same file and `src/compiler/80.driver/driver_source_pipeline_parsing.spl` | Environment effect; `(text) -> text` in source loading and `(text) -> text?` in parsing; trace/entry settings and parse controls → driver → D | Reconcile these two declared result shapes through a single host-service view; preserve existing unset defaults and per-process caching. |
| `rt_file_read_text` / `rt_file_read_text_rv`, `src/compiler_rust/compiler/src/interpreter_extern/{mod,file_io}.rs` | Seed dispatch; `(&[Value]) -> Result<Value,CompileError>`; registry entries at `mod.rs` 1491/1503 → Rust file handler → I | Two registered names currently share the Rust handler. Native C has separate text and RuntimeValue ABI entrypoints; cross-engine value ownership and failure mapping need a differential fixture. |
| `rt_fd_pread` / `rt_fd_pwrite`, same Rust registry and `file_io.rs` | Raw positioned descriptor effects; `(&[Value]) -> Result<Value,CompileError>`; `sosix_posix_*` SFFI → seed handler → I | Covered in the positioned-I/O manifest. Retain exact byte-count/error semantics and compare seed/native/SimpleOS routes without treating the Rust seed as product verification. |
| `rt_process_run`, `rt_process_run_bounded`, `rt_process_run_timeout`, `src/compiler_rust/compiler/src/interpreter_extern/{mod,system}.rs` | Seed process effects; `(&[Value]) -> Result<Value,CompileError>`; `std.nogc_sync_mut.io.process_ops`/`io_runtime` → Rust system handler → I | The registry is hand-maintained beside native process implementations. A shared SOSIX operation description must bind tuple shape, limits, timeout, output bounds, cancellation, and error conversion. |
| `rt_file_read_text` / `rt_file_read_text_rv`, `src/runtime/runtime_native.c` | Native hosted file effects; byte-path ABI versus RuntimeValue ABI → C runtime → N | C exports are distinct; the seed registry alias does not prove ABI equivalence. Preserve the correct caller ABI and source/error ownership during migration. |
| `rt_env_get` and `rt_process_run`, same C runtime | Native hosted environment/process effects; native text/array ABI → C runtime → N | Keep native effects behind a provider boundary, with exact cold-start and process-result behavior. Source presence does not show that D and I use one generated contract. |
| `native_mmap_file`, `src/compiler/99.loader/loader/{smf_cache,smf_mmap_native}.spl` and `src/compiler/99.loader/smf_mmap_native.spl` | File mapping; `(text,i64,i64,i64,i64) -> (i64,i64)` adapter → `[i64]` owner → `rt_open_fd`/`rt_mmap_raw`/`rt_close_fd` → L/N | Preserve mapping extent, descriptor close, failed-map sentinel, cache lifetime, and lazy first-use behavior. Map/close parity on interpreter and native remains unqualified. |
| `native_make_executable` / `native_make_rw`, same loader adapters | Protection changes; `(i64,i64) -> bool`; SMF/JIT mapping → `rt_mprotect` owner → L/N | SOSIX VM capability must retain W^X, executable identity, in-flight pins, and explicit retirement. A generic file-service replacement cannot own this lifetime. |
| `moduleloader_ensure_{compiler_ctx,obj_taker,provider,jit,loader_mapper,lifecycle}`, `src/compiler/99.loader/loader/module_loader_services.spl` | Lazy service creation; `(LazyModuleLoader) -> service`; public module loader → loader-owned cells → L | Keep zero optional service creation on cold paths. Migration must inject services without an eager compiler/JIT/mapper cycle. |
| `moduleloader_allocate_exec_module`, same file | Executable allocation; `(LazyModuleLoader,text,text,[u8],bool) -> i64`; loaded SMF symbol → loader mapper/JIT exec mapper → L | Preserve owner ID, symbol replacement policy, mapped bytes, release ordering, and generation pins before SOSIX VM routing. |

## Boundary findings and next evidence

1. `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` manually registers
   these seed handlers, while the native runtime and Simple driver declare
   their own ABIs. RU-040 must produce one canonical operation description and
   prove interpreter/native results; a matching `rt_*` spelling alone is not a
   shared service contract.
2. RU-041 should inject granted file, environment, and process services behind
   the existing driver descriptor, then compare source ordering, diagnostics,
   cache keys, entry closure, and multiple target backends. The listed D
   source/environment routes are not yet routed through SOSIX; the separate
   `src/compiler/80.driver/cache/worker/three_payload_worker_io_v1.spl`
   in-memory worker already has a SOSIX route.
3. RU-042 must preserve the loader's lazy service creation, mapping ownership,
   W^X transitions, unload pins, and bootstrap recovery. The current L path
   still uses direct runtime SFFI for file descriptors and virtual memory.
4. This family omits renderer/input, network, GPU, most interpreter externs,
   and other loader imports; RU-001 global census remains open. Qualification
   requires a source-matched pure-Simple runner and native/interpreter/SMF
   differential evidence, not this source inventory.
