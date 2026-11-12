# Windows Stage 2 compiler rejects its own array handles: native_all + core-C supplement resolve to mixed owners

- Status: fix-implemented (seed linker + 2 C exports); lane proof pending
- Found: 2026-11-12, Windows Stage 2 trust-root lane on `71ea8b2` (release/1.0.0)
- Component: `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` (Windows core-c-bootstrap layering), `src/runtime/runtime_native.c`

## Observation

Stage 2 compiled all 1636 modules, linked, and answered `--version`
(`simple-bootstrap 1.0.0-rc.1`). Its first real compile, the `scv-prime`
sanity (`native-build --runtime-bundle core-c-bootstrap --mode one-binary
--entry p2_add.spl`), printed at startup

```
[simple-runtime][error] rejected invalid array handle before dereference; probable compiler/FFI ABI mismatch (value_bits=0x0000025b209a0f61)
workarounds: incomplete coverage; run simple check-dbs --fullscan bugs
```

then ran single-threaded (1.6 GB, 100% of one core) with no further output
until the 1800 s bound (`frontend_status=124`). `p2_add` never ran. The
binary is preserved as `stage2/x86_64-pc-windows-gnu/simple.exe.rejected`.

## Root cause

The Windows link lists `libsimple_native_all.a` (Rust runtime + Rust
compiler) first and the core-C supplement `simple_runtime.lib`
(runtime_native.c compiled with `SIMPLE_CORE_C_STANDALONE=1
SIMPLE_RUNTIME_MEMORY_OWNER=1`) second under `--allow-multiple-definition`,
intending "native_all wins every shared symbol, the supplement only supplies
the C-only entry points" (linker.rs TODO `[driver][P2] Establish which runtime
actually wins a hosted link`). But archive members are extracted lazily, and
first-definition-wins is decided by extraction order: when
`runtime_native.obj` is pulled for a C-only root (`rt_iocp_create`,
`rt_process_*`, ...), every shared symbol it defines that no already-loaded
object had referenced yet becomes the first definition. llvm-nm census on the
real link inputs: 975 `rt_*` referenced by the Stage 2 closure, 774 defined by
BOTH archives, 126 only by the supplement; 26 of the shared ones read arrays
through runtime_native.c's private registry (`rt_core_as_array`, which only
admits its own allocations). A Rust-owned array reaching one of those C copies
is exactly the message above; the caller then loops on the rejected result.

Independently of the race, two C-only exports the compiler closure uses
decoded `text` handles through the private registry and could never accept a
Rust-owned string: `rt_text_is_ascii` (fell back to treating the tagged
pointer as a raw `char*`) and `rt_file_list_dir` (returned nil for every
directory). The ELF lanes do not see any of this: the Linux capsule branch
roots every native_all-owned symbol the supplement also carries before the
supplement is scanned, and ELF weak semantics let the C copies lose.

## Fix

- `linker.rs`, Windows `is_native_all` branch: when the bundle is
  core-c-bootstrap, build the supplement first, read both defined-symbol sets
  (fail closed when either is empty), find the native_all MEMBERS that define
  a symbol both archives define (`nm -A`), extract them with `llvm-ar x` and
  list them as plain objects ahead of both archives. Objects are defined the
  moment they are read, so no member-extraction order can override them.
  First attempt (PR #8436) only added the shared symbols as `-u` roots; the
  rebuilt Stage 2 still resolved 181 of them (rt_utf8_validate, rt_atexit_*,
  rt_io_udp_*, ...) into the supplement, because lld-COFF handles `/include`
  after the input-file resolution loop, by which time runtime_native.obj
  (fetched for a C-only reference) had already supplied the first definition.
  lldb on the rejected binary: `rt_core_report_invalid_array_once` <-
  `splc_utf8_array_to_bytes` <- `rt_utf8_validate` (C copy) <-
  `text_bytes.utf8_bytes_valid` <- `external_text_decode` <- host_limits file
  read at native-build startup. The roots stay (harmless) in a response file.
- `runtime_native.c`: `rt_text_is_ascii` and `rt_file_list_dir` read the
  handle through `rt_string_len`/`rt_string_data` (`core_text_dup_abi`),
  which resolve to whichever runtime owns strings in the link.

Remaining C-only exports that still decode privately and are referenced by the
compiler closure: `rt_http_get`, `rt_http_download` (not on any bootstrap
path). The TODO in linker.rs stays until a measured census replaces the
"first definition" assumption with a verified owner list.

## Evidence / specs

- Reproducing: the Windows Stage 2 lane sanity on `71ea8b2` (log
  `stage2-sanity.env.frontend-failure.log`, `frontend_status=124`); the
  rooted relink is proved by the same lane admitting Stage 2.
- No unit spec models two-archive COFF extraction order; the closure-strict
  pass of `check-runtime-link-completeness.shs` (PR #8414) covers the
  neighbouring class (undefined, not mis-owned, symbols). A per-symbol owner
  census gate is the follow-up named by the linker.rs TODO.
