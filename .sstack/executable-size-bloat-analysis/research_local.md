# research_local.md — Track A: CC/LD Invocation Tracing

*Status: COMPLETE — 2026-04-28*

---

## 1. Wrapper Chain

`bin/simple` is a bash script (`bin/simple`, full content). It:
1. Looks for a Rust-compiled binary at `src/compiler_rust/target/bootstrap/simple`, then `target/release/simple`, then pre-built platform binaries in `bin/release/<triple>/simple`.
2. `exec`s the first one found, forwarding all arguments unchanged.
3. The Rust binary (`simple-driver`) is the real compiler. It is **NOT** an interpreter-only system — it has a full native-codegen path.

**Codegen paths inside the Rust binary:**
- **Interpreter / SMF mode**: the default for `bin/simple run <file.spl>` — interprets bytecode.
- **Native codegen** (`--mode=native` / `bin/simple build`): invokes the Cranelift (default) or LLVM (`SIMPLE_BACKEND=llvm`) backend, emitting real `.o` object files, then links them via the system C compiler.

To trigger native codegen: `bin/simple build` (bootstrap/project builds) or `NativeProjectBuilder` API (Rust code path: `src/compiler_rust/compiler/src/pipeline/native_project/`).

---

## 2. CC/LD Invocation

### 2a. Runtime C sources → object files

Source: `src/compiler/70.backend/backend/runtime_compiler.spl`, lines 155–230.

Compiler discovery: `SIMPLE_CC` env var → `/usr/bin/clang` → `/usr/bin/gcc` → PATH search for `clang`, `gcc`, `cc`.

**Compile command per runtime .c file (GCC/Clang, Unix):**
```
<cc> -c -fPIC -ffunction-sections -fdata-sections [-Oz|-O2] -I <rt_dir> -I <rt_dir>/platform -o <tmpdir>/simple_rt_<name>.o <rt_dir>/<name>.c
```
(`-Oz` when `opt_size=true`, else `-O2`. **No `-g` flag** — runtime objects are compiled without debug info.)

Sources: `runtime.c`, `runtime_native.c`, `runtime_thread.c`, `runtime_memtrack.c`, `async_driver.c`, `runtime_fork.c`
(`src/compiler/70.backend/backend/runtime_compiler.spl:175`)

### 2b. User .spl files → object files

Source: `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs` (Cranelift backend, default) or LLVM backend (`SIMPLE_BACKEND=llvm`).

Cranelift emits `.o` files directly via the Cranelift object writer — no intermediate C. LLVM backend (`LlvmBackend`) emits LLVM IR then calls LLVM's object emitter. Neither path runs `cc -c` on user code; the Rust codegen emits `.o` directly. **No `-g` is passed in codegen** (debug info not inserted at this stage by default).

The `main` stub (generated C++) IS compiled with:
```
<cxx> -c -ffunction-sections -fdata-sections -o <main.o> <main.cpp>
```
(`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:318`)

The init-caller stub (`__simple_call_module_inits`) is compiled with:
```
<cxx> -c -ffunction-sections -fdata-sections -o <init_caller.o> <init_caller.cpp>
```
(`linker.rs:411-412`)

### 2c. Final link step (Linux/FreeBSD, primary path)

Linker selection: tries `mold` > `lld` > system `ld` directly; falls back to `cc` driver if CRT not found.

**Direct linker path** (`link_native_unix`, `linker_wrapper.spl:135-303`):
```
<mold|lld|ld> -m elf_x86_64 -dynamic-linker /lib64/ld-linux-x86-64.so.2
    [CRT files] [user .o files or libspl_objects.a with --whole-archive/--no-whole-archive]
    -L<runtime_dir> -lsimple_runtime [system libs]
    --gc-sections
    [-g if config.debug]
    [-s if config.strip]
    -o <output>
```
(`linker_wrapper.spl:203-274`, `linker.rs:684,742-753`)

**cc fallback path** (`link_native_cc`, `linker_wrapper.spl:464-530`):
```
cc <user.o files> -L<runtime_dir> -lsimple_runtime -lsimple_compiler -lc -lpthread -ldl -lm
    -Wl,--gc-sections
    -o <output>
```
(`linker_wrapper.spl:519-521`)

**NativeProjectBuilder Rust path** (`linker.rs:684`):
```
<cc/cxx> [object_archive with --whole-archive] [runtime_lib] -Wl,--gc-sections
    [-Wl,-s if strip=true]
    -o <output>
```

---

## 3. Section Flags

| Flag | Runtime .c objects | User .spl .o files | Link step |
|------|--------------------|--------------------|-----------|
| `-ffunction-sections` | YES (`runtime_compiler.spl:207`) | N/A (Cranelift emits directly) | — |
| `-fdata-sections` | YES (`runtime_compiler.spl:208`) | N/A (Cranelift emits directly) | — |
| `-Wl,--gc-sections` | — | — | YES (`linker_wrapper.spl:521`, `linker.rs:684`) |
| `-Wl,-dead_strip` | — | — | macOS equivalent (`linker_wrapper.spl:519`) |
| `-flto` / LTO | NO | NO | NO |
| `-Wl,-s` / strip | — | — | Only if `config.strip=true` (`linker.rs:746`) |
| `-Wl,--icf=safe` | NO | NO | NO |

**Critical gap**: Cranelift-compiled user `.o` files do NOT go through `cc -c` with `-ffunction-sections -fdata-sections`. Cranelift emits object files directly via its own object writer. Whether each function gets its own `.text.<fn>` ELF section depends on Cranelift's own object-emission settings — this is NOT controlled by `-ffunction-sections`. If Cranelift emits all functions of a module into a single `.text` section, `--gc-sections` cannot strip individual dead functions.

**`strip` defaults to `false`** in `NativeBuildConfig::default()` (`native_project_mod.rs:175`). The default `bin/simple build` does NOT strip the binary.

---

## 4. Runtime Archive

The pre-built `src/runtime/libsimple_runtime.a` is a static archive. When the Rust native build pipeline runs, it selects the runtime via `selected_runtime_library()` (`linker.rs:452`).

**Key problem**: On Linux/FreeBSD, when the runtime is a `native_all` library (the "all-in-one" prebuilt), the env var `SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1` causes `-Wl,--whole-archive <runtime.a> -Wl,--no-whole-archive` — which forces ALL runtime symbols to be linked in, defeating `--gc-sections` entirely (`linker.rs:652-655`). Without the env var, `runtime_roots` (partial symbol selection) is used instead.

The user-code object archive (`libspl_objects.a`) is **always** linked with `--whole-archive` / `--no-whole-archive` (`linker.rs:610-612`) because module-init functions must run. This means every TU's code survives the link — `--gc-sections` cannot prune between them.

---

## 5. Debug Info

- **Runtime C objects**: compiled with `-O2` or `-Oz`, **no `-g`** (`runtime_compiler.spl:205-208`).
- **User code (Cranelift)**: Cranelift does not insert DWARF debug info by default (no `-g` equivalent passed; debug mode not set in default `NativeBuildConfig`).
- **User code (LLVM)**: LLVM backend's debug mode depends on `LlvmBackend` configuration; not forced on by default.
- **`config.strip` defaults to `false`** — binary not stripped after linking.
- **Release-vs-debug distinction**: `NativeBuildConfig.strip` must be set explicitly. In `linker_wrapper.spl`, `-g` is added only `if config.debug` (`linker_wrapper.spl:273-274`). The default `NativeLinkConfig.debug` is `false` (`linker_wrapper.spl:65`).

There is NO automatic strip pass. The binary retains any debug sections emitted by the backends.

---

## 6. Self-Registering Tables

The compiler emits `__module_init_<module_name>` functions for every compiled module. These initialize string global variables (`common_backend.rs:941-962`). In LLVM mode, they were registered via `.init_array` — but that path is now skipped (`common_backend.rs:1058`).

Instead, the **native build pipeline** scans all object files with `nm`, collects every `__module_init_*` symbol, generates a C++ file with `__simple_call_module_inits()` that calls all of them explicitly (`linker.rs:331-387`), compiles it with `-ffunction-sections -fdata-sections`, and links it in.

**This is the critical DCE-defeating pattern**: because `__simple_call_module_inits` calls every module's init function by name, and all module init functions are explicitly referenced, the linker's `--gc-sections` cannot eliminate any module that has string globals — every such module's code is retained. This is structurally equivalent to a `__attribute__((constructor))` for every TU.

`strip_llvm_constructors` (`tools.rs:243`) strips `.init_array` sections from object files to avoid double-init — but the explicit call via `__simple_call_module_inits` is the canonical init path.

Additionally, user-code objects are packed into `libspl_objects.a` and linked with `--whole-archive`, which forces every symbol from every TU to be linked in regardless of reachability.

---

## Summary

- **`--gc-sections` IS passed** at the link step (Linux/FreeBSD: `linker_wrapper.spl:521`, `linker.rs:684`). The flag is present.
- **`-ffunction-sections`/`-fdata-sections` gap for user code**: Runtime C objects get these flags. Cranelift-emitted user `.o` files do NOT go through `cc -c`; whether Cranelift puts each function in its own section is controlled by Cranelift's codegen settings, not by these flags. If Cranelift coalesces functions into a single `.text` section, `--gc-sections` cannot prune individual functions.
- **`--whole-archive` on user object archive** defeats `--gc-sections` for user code: `libspl_objects.a` is linked with `--whole-archive`/`--no-whole-archive`, forcing every compiled TU's symbols into the binary (`linker.rs:610-612`).
- **`__module_init_*` explicit call table** pulls in every module's init functions by explicit reference (`linker.rs:346-387`), preventing any module that has string globals from being dead-stripped.
- **No LTO, no ICF, no strip by default**: `-flto` is not used; `-Wl,--icf=safe` is not used; `config.strip` defaults to `false` — binary is not stripped.
