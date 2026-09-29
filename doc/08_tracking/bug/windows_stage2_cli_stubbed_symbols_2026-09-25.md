# Windows stage-2 full CLI links through stubbed unresolved symbols (tracked debt)

- Date: 2026-09-25
- Status: OPEN, tracked debt. Accepted by owner decision "parity now + fix later".
- Lane: `native-build --runtime-bundle host-gpu` on `x86_64-pc-windows-msvc` (clang-cl + lld-link).
  - Entry: `src/app/cli/_CliMain/main_and_help.spl` (bootstrap-phase-verification `compiler_cli_build`).
- Seed change: `pipeline/native_project/{linker.rs,stubs.rs,tools.rs}`, branch `work/win-stub-parity-20260925`.

## What happens

bootstrap30 compiled 2418/2418 modules and then failed the link on 553 undefined symbols.

The same object set links on Linux because of two differences:
- **Linux:** the LLVM backend gives every body its own ELF section, and ELF resolves undefined symbols
  after `--gc-sections`. A reference that only unreachable code makes is dropped with that code.
- **Windows:** lld-link reports every undefined symbol before `/OPT:REF`. Simple's COFF bodies are not
  COMDAT: most are `weak`, and a weak COMDAT would stop a strong definition from overriding them.

The seed now handles this on Windows with MSVC in strict mode (`SIMPLE_NO_STUB_FALLBACK=1`):
1. The first link runs with `/errorlimit:0`.
2. If it fails on undefined symbols, the undefined names are split:
   - Rust std/alloc internals: never stubbed. The link fails if any remain.
   - Everything else: compiled with clang-cl into trap stubs, and the link is retried once.
3. Each stub prints `fatal: called unresolved symbol `<name>`` and aborts if it is ever called.
4. The build prints `[native-link] stubbed N unresolved symbol(s) ...` and writes the full list to
   `<output>.stubbed_symbols.txt`.

## Remaining difference from Linux (the debt)

- **Reachable references:** ELF still rejects an unresolved reference from reachable code at link time.
  Here it links, and fails loudly only when the stub is called.
- **Fix-later path:** make weak bodies GC-able on COFF, then reject any stub that survives `/OPT:REF`
  (lld `/MAP` liveness).
  - A plain weak COMDAT (`comdat any`) is not an option: measured, it turns weak-vs-strong overrides into
    `duplicate symbol` errors.

## Class F: Rust std / allocator internals (never stubbed)

The hosted runtime rlib's Windows-only `win32` module uses std (`Mutex`, `HashMap`, `eprintln!`), and a bare
`.rlib` carries no std and no `__rust_alloc` shim. This left 28 std/core/alloc/hashbrown internals undefined.

- **Fix, part of this change:** the host-gpu Windows link adds an empty `staticlib` built by the SAME rustc
  that built the rlib (the version is read from the rlib metadata). It bundles exactly std + the allocator shim.
- **Fail fast:** a version mismatch fails with an install hint.

## Stubbed classes at bootstrap30 (525 names), by owner follow-up

Measured by relinking the kept bootstrap30 objects.
- **Before the change:** 553 undefined. 28 were Rust internals, resolved by the std shim.
- **After:** 525 stubbed, 0 undefined, links.

Full per-symbol data came from the analysis `stage2_cli_link_undefined.md`.

- **A. `rt_*` implemented only in the Rust runtime (192):** `rt_cli_run_*` / `rt_cli_handle_*`, cuda (36),
  metal (30), vulkan (~62), winit (10). To be feature-gated (owner decision 2).
- **B. `rt_*` implemented only in C files outside the core-C lane (207):**
  - sdl2 (72), rocm (31), sqlite (26; must be backed by the embedded engine per `CLAUDE.md`, never libsqlite3),
    dynload (24), async_driver (14);
  - `platform_win.h` fd/mlock (6), `runtime_process.c` dap (4);
  - bare-metal/freestanding `rt_port_*` / `rt_lgdt` / `rt_mmio_*` (24).
- **C. Defined nowhere (90):** `rt_http_*` (15), `rt_oneapi_*` (10), `rt_intel_*` (10), `rt_engine2d_*`,
  `rt_ws_*`, `rt_webgpu_adapter_*`, `process_*` (4, `app/io/rt_hal_isolated_host.spl`), `compare_cells_for_sort`,
  `glob_matches`, `path_components`, `file_metadata`, ...
- **D. Simple functions not linked (12):**
  - `path_parent` / `path_filename` (wrong import);
  - `rt_hal_unavailable_*` used as values (compiler);
  - `rt_term_*`, kernel pmm/vmm, `_gpu`.
- **E. Simple methods / variants (26):**
  - `DocBlock::*` (enum does not exist), `RichTextEditor.convert_to_*`, `EditSession._find_doc_index`;
  - `*_fn` struct-field calls lowered as methods (compiler), `text.from_bytes` / `text.from_char_code`.

Every stubbed name is a real gap. The fix is to feature-gate or implement at the source (follow-up package set
P2-P10 in the analysis). This file closes when the full CLI links on Windows with `stubbed 0`.
