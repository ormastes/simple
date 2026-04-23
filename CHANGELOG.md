# Changelog

All notable changes to Simple Language will be documented in this file.

## [0.9.6] - 2026-04-22

### Added
- **VHDL backend** — full `source`-facade subset with process/aggregate/switch lowering, casts/shifts/rem/bitnot, if-else result mux, goto-return chains, `@vhdl` compile support, source-to-VHDL combinational subset
- **Driver framework (FR-DRIVER-0001..0006)** — `@driver` / `@native_lib` attribute sugar, `DrvManifest` section + encoder, `rt_dma_*` primitives for x86_64/x86/arm64/arm32/riscv64/riscv32, GPU-adapter forwarding with tolerant `init_all`
- **SimpleOS** — x86_64 GUI hello-world boot path, aarch64 fs-exec bootstrap spawn/scheduler, APIC topology, compiler-driver + SPM request wiring, `rt_memcpy` ELF loader
- **Window manager (v31–v50)** — desktop, dock, PS/2 input, vector/procedural/pixel-level paint, PPM decoder, terminal, browser window, focus + 12/15 shared-module rollout
- **Browser platform** — `ui.browser` / `ui.web` / `ui.tui_web` wired to shared modules, Blink/Skia/cc/viz-style naming, WebGPU compute-draw extern, WebKit-style completions, WSS handshake + TLS v1.1/v1.2 hardening
- **Font rendering** — TTF path end-to-end, `fontrasterizer` into `font_renderer`, glyph coverage for measurement, `SIMPLE_TTF_DYLIB`/`_PATH` env opt-ins
- **Declarative UI access**, **Cocoa + Win32 hosted** surfaces, **Rust stage1 sysroot** (`x86_64-unknown-simpleos`)
- **MDSOC+** default for userland (ECS business layer), **spostgre phase 9**, **traceability + bug_review** tooling
- **`--compile` / `run_test_file_native_mode`** wiring, **package registry** scaffolding

### Fixed
- **aarch64 bootstrap** — remove x86 inline asm from `interrupt.spl`
- **VHDL lowering** — switch return targets, goto-return chains, unsupported-stateful MIR diagnostic, tuple/enum aggregates, scalar source-facade width ops
- **Cross-module fieldget crash** workaround, **MIR method dispatch** widening, **vtable ABI** + static dispatch
- **Windows MCP server loading**, **MCP startup** rename/stabilization, **simple mcp + lsp diagnostics**
- **virtio-net** vendor check + RX queue, **WebSocket handshake**
- **Host + SimpleOS renderer** validation, **qemu timeout output** preservation, **resident desktop launch**
- **Wrapper sentinel cache** + triple-quoted string use, **glyph coverage** use for match-arm canonicalization
- **Submodule gitlink flips** (jj ↔ git), **watchdog memory limit** disable for long bootstraps

### Changed
- **Module splits to ≤800L** — `vulkan_graphics_runtime.rs` (2221→9), `linker/native_binary.rs` (2177→submodules), `codegen_instr_tests.rs` (2277→7 by instruction), `checker.rs` (2502→7), `html_tree_builder.spl` (2784→6) + `css_parser.spl` (1090→4), `winit_ffi.rs` (1767→6), `collections.rs` (4), `error.rs` factory, plus coverage-spec splits (string_core, math_repr, cbor, color_coverage, parsers/date/serialization)
- **SimpleOS QEMU targets** routed through platform catalog, **shared platform console** extracted
- **Host adapter contract** extracted, **host surface kinds** + **native event marker** centralized
- **ELF loader** — per-byte segment copy replaced with `rt_memcpy` bulk primitive
- **Untracked auto-generated artifacts** — launcher symlinks, platform-specific mcp/t32 links, setup-generated entries, binaries/build carryover
- **Replace string dict keys** with enum/id variants in hot paths
- **Share query helper parsing** across host and QEMU renderers
- **Split `wm_entry`** by init phase; **unify WM rendering**

## [0.9.5] - 2026-03-29

### Added

### Fixed

### Changed

## [0.9.4] - 2026-03-28

### Added

### Fixed

### Changed

## [0.9.3] - 2026-03-28

### Added
- **Traceability module** — requirement-to-test tracking with SDN config
- **Verify/Sync/Debug skills** for Claude Code workflow
- **Release skill** with full GH Actions pipeline docs and `/release` invocation

### Fixed
- **~200 broken tests** — dict indexing, Slice.len(), interpreter chaining bugs
- **codegen_parity** Future/Await/Generator/Actor hang in interpreter (skip_it)
- **bin/simple_mcp_server** updated to use bin/simple or platform-specific release binaries
- **bin/simple symlink** fixed via setup.sh for aarch64-apple-darwin-macho

### Changed
- Cleaned 10 orphan jj commits and 2 stale remote push branches
- Test database lock cleanup

## [0.9.2] - 2026-03-22

### Added
- **mLLVM_QEMU unified compiler backend** — guest decoders (AVR + 8086), x86_64 host backend, optimizer passes, binary format serialization, linker, emulation runtime
- **mLLVM_QEMU IrTc backend integration** into Simple compiler with MDSOC transforms, width libraries, and test suite
- **Full-feature async UI framework** — 21 widgets, 4 backends (Electron/Tauri), lifecycle hooks, 10 demo apps
- **Headless UI system test infrastructure** with widget rendering verification
- **Platform-aware bootstrap layout** with setup script, verified on macOS
- **Windows LLVM-lib backend**, linker, test runner, MCP shell port
- **SMF (Simple Module Format)** — manifest writer, cache loading, dependency validation

### Fixed
- **UI framework backends** — interpreter workarounds, SDN tree parser, IPC protocol rewrite
- **Rust seed parser compatibility** — remove dotted exports and chained field access
- **Tauri integration** — end-to-end widget rendering in Tauri window
- **Cranelift Mach-O corruption** — `define_zeroinit` → `define` for data with relocations
- **macOS** `_dot_` suffix in method resolution, Mach-O define_zeroinit fix
- **FreeBSD cross-compile** shell syntax, deduplicate MSVC lib path discovery
- **module_init** via constructor function instead of `.init_array`
- **nil-guards** for parser/lexer module-level var arrays
- **EffectSolver** free function wrappers, skip effect pass for bootstrap

### Changed
- Platform-aware binary layout with `bin/release/<triple>/simple` organization

## [0.8.8c] - 2026-03-09

### Added
- **TRACE32 GUI-to-CLI converter** + MCP servers — 2 implementations, 1 converter, 2 MCP servers
- **Resource safeguard monitor** — cross-platform `kill_simple_monitor` (Linux/macOS/FreeBSD/Windows/MinGW/MSVC), test runner integration
- **Platform-specific MCP config** — auto-detect OS for `.mcp.json` install

### Fixed
- **Comprehensive CRLF→LF normalization** at all source file read points — resolves 1054 stage1→stage2 parse failures
- **CRLF handling in Rust lexer** + stale jj conflict markers
- **Rust parser** — handle `pass_do_nothing`/`pass_dn`/`pass_todo` as keywords
- **FreeBSD bootstrap** — stub generation, library linking, main shim args, `rt_cli_get_args`
- **Windows COFF object support** + atomic handle counters
- **Windows Cranelift calling convention** + memory leak fixes
- **Windows bootstrap** — rewrite `.bat` for Rust seed pipeline, fix `native_project.rs` for MSVC
- **MCP server** — file URI parsing, getcwd crash, shape string interpolation, Windows compatibility
- **Test runner** — resource check (25% free threshold), self-protection, sequential execution on non-Linux platforms
- **49 test failures** resolved — macOS compat, QEMU guards, interpreter-mode skip patterns
- **5 pre-existing test failures** — capability tests for bootstrap mode, env-dependent tests
- **`native_project.rs`** — handle `--key=value` arg forms, differentiate clang-cl vs MinGW linker flags

### Changed
- **Unified DAP server** via `DebugAdapter` trait — eliminated 17 conditional branches
- **Reorganized `doc/guide/`** — merged 175 files into 42, topical subdirectories
- **Cleaned `test/` folder** — removed 3343 SMF build artifacts, 11 stale dirs
- **Renamed `.ssh` → `.shs`** extension (Simple Shell) to avoid SSH protocol confusion
- **Removed obsolete seed/C bootstrap** — CI now Rust-only
- **Removed `.mcp.json`** files from tracking (gitignored)

### Security
- Removed server credentials file from repo

## [0.8.1] - 2026-03-05

### Added
- **Windows native binary** in release workflow — Rust bootstrap builds `simple.exe` natively on `windows-latest`
- **Windows cross-compile binaries** — MinGW cross-compilation for `windows-x86` (i686) from Linux
- **Windows aarch64 binary** — MSVC cross-compilation for ARM64 Windows
- **Cross-platform bootstrap doc** — updated `doc/guide/bootstrap.md` with macOS/Windows platform notes and backend summary table

### Fixed
- Release workflow now produces Windows `.exe` binaries instead of source-only packages
- Distribution packages use correct `.exe` extension for Windows platforms
- Bootstrap doc section renamed from "Linux Bootstrap Stages" to platform-agnostic title

## [0.8.0] - 2026-03-02

### Added
- **Self-hosting Stage 3**: Simple compiles itself — full self-hosted bootstrap achieved
- **Cranelift backend**: Multi-backend bootstrap support (LLVM + Cranelift)
- **JIT default**: Changed default execution mode from Interpret to JIT
- **`new` keyword** for explicit allocation (Phase 1)
- **`#[alloc]` / `#[no_alloc]`** function attributes (Phase 2)
- **Alloc inference pass** for automatic allocation tracking (Phase 3)
- **Collection efficiency lint** + MIR optimizer passes (COLL001–COLL005)
- **25+ new MCP tools**: CLI, query, analysis, LSP (34 → 66 tools total)
- **AST pattern matching** + semantic queries (CodeQL-style `sem-query`)
- **Multiplatform linker abstraction** for Windows, macOS, FreeBSD, multi-arch
- **Tiered library structure** (alloc, sys, async, ext)
- **Tiered runtime FFI classification** for target-aware symbol filtering
- **Native-build command** with name mangling, re-export resolution
- **SMF relocation metadata** for unified JIT + native loading
- **Ruby-like lambda features**: placeholder transform (`_ * 2`), `&:method` refs, curry/partial
- **WFFI dynamic loading** support
- **LLVM cross workflow** for Linux/Win/FreeBSD/macOS
- **Baremetal modules** and `rt_compile_to_llvm_ir` via CompilerDriver + MirToLlvm
- Type system Wave 2: flow narrowing (M2), associated types (M3), effect system (M4)
- Bitfield feature — hardware register definitions with zero-overhead bit manipulation
- Pass keyword variants: `pass_do_nothing`, `pass_dn`
- Rust parser extensions: asm, bitfield, newtype, extend, comptime, backtick atoms
- `slow_it` test marker for filtered slow test runs

### Changed
- Default execution mode: Interpret → JIT
- Migrated business logic from `app/` to `lib/` and `compiler/` (Phases 0–5)
- Split all 800+ line files into smaller modules
- Removed ~200 semantically duplicated files across `src/`
- Renamed 39 adhoc `_ext` test files to descriptive names
- Normalized `str` → `text` type annotations across codebase
- Switched primary VCS documentation from git to jj
- MCP server: lazy imports, proxy removal for faster startup
- Multiplatform & multi-CPU support for Rust bootstrap compiler
- Fully self-sufficient binary — eliminated all `bin/simple` subprocess calls
- Release binary download fallback added to bootstrap and CI

### Fixed
- Deterministic Cranelift codegen for reproducible bootstrap
- MCP server shell tools (interpreter tuple returns)
- Cross-platform compilation for Windows, FreeBSD, and macOS bootstrap
- 4 interpreter fixes to unskip 37 test files (+696 tests)
- Recovered ~77 test files from skip + added specific skip reasons
- Prevented test suite hangs and OOM with memory abort
- Added missing timeouts to MCP tool subprocess calls
- Cleared compiler-side static registries between test runs (OOM fix)
- Resolved 220+ failing tests across multiple files
- Database_sync and codegen_parity test failures
- Cranelift codegen: reuse declared extern funcs, add diagnostics
- Module loader crash bugs + memory efficiency improvements
- Heap-allocation leaks in MIR C codegen
- Lint false positives for True/False enum variants

### Infrastructure
- Self-hosted bootstrap: no fallback for JIT, SMF loader, native builder
- Bootstrap binary updated for self-hosting
- `build/bootstrap/c_simple/` as canonical bootstrap location
- Interpreter optimizations for faster test runs

## [0.7.0] - 2026-02-24 (unreleased)

_Merged into 0.8.0 — see above._

## [0.6.1] - 2026-02-23

### Added
- Async I/O driver infrastructure with platform backends (epoll, io_uring, kqueue, IOCP)
- Sanitizer CI workflow (ASan builds)
- Valgrind check script
- Optimized build script

### Changed
- Mass test suite repair: +831 passing test cases across all suites
- MIR codegen trait unification (C/LLVM shared trait)
- All stale version references updated from 0.5.0 to 0.6.1

### Fixed
- Memory leak elimination across all 9 categories (slice, substr, lex args, program args, etc.)
- C backend string escaping and C++ keyword safety
- Runtime intrinsics for codegen
- Test runner binary resolution
- Parse errors in test files

### Infrastructure
- Bootstrap build updated to use v0.6.0 as base
- 11-platform release matrix (added FreeBSD x86, Windows x86, Windows ARM64)

## [0.6.0] - 2026-02-14

### Added
- Grammar documentation system with tier-based keyword tracking
- Thread pool worker implementation complete (100% coverage)
- Threading integration with startup/bootstrap systems
- Windows build system with MinGW and ClangCL toolchains
- Module loading investigation and fixes
- File stat implementation for runtime (rt_file_stat)
- Grammar specification files (core, full, seed, tier keywords)
- Tree-sitter grammar status documentation
- Comprehensive test coverage (4067/4067 tests passing - 100%)

### Changed
- Bootstrap workflow now uses v0.5.0 release for reproducible builds
- Release workflow enhanced with automatic runtime building
- Test coverage improved from 3916 to 4067 tests (+151 tests)
- Platform library integration verified with zero regressions
- Documentation coverage system marked production ready

### Fixed
- 8 timeout issues in test suite (all resolved)
- Module-level import and closure issues
- Bootstrap rebuild activating transitive imports
- Package management Result→tuple conversion
- Platform detection and newline handling

### Documentation
- 10+ comprehensive status reports added
- Grammar reference documentation complete
- Windows build guides (quick start + detailed)
- Threading implementation documentation
- Bootstrap status and progress tracking
- Implementation completion report (92% core features)

### Infrastructure
- GitHub Actions workflow updated for 0.6.0 release
- Multi-platform bootstrap packages (7 platforms)
- Automated testing with downloaded v0.5.0 bootstrap
- Release artifact creation and publishing to GHCR

### Test Suite
- **100% pass rate**: 4067/4067 tests passing
- Platform abstraction: 80/80 tests (100%)
- Package management: All tests fixed and passing
- Effect system: Production ready
- Parser error recovery: Comprehensive coverage
- Zero test regressions

## [0.5.1-rc.1] - 2026-02-11

### Added
- Async/await parser implementation (Phases 1-7 infrastructure complete)
- VHDL backend with verification constraints and tests
- VHDL examples, golden files, CI integration, and user guide
- Test enablement progress tracking documentation
- Expression slice evaluation support in interpreter (Phase 1.1 partial)

### Changed
- MCP server enhanced for production readiness with robustness improvements
- Generic template tests enabled (5 tests - Phase 1.3 validation)
- Deep learning config system improved for runtime compatibility

### Fixed
- MCP server crashes: prompts/get (enum match), bugdb, uri templates
- Runtime compatibility issues with reserved keywords
- DL config default function replaced with standalone for runtime compatibility
- FFI skip test and SFFI wrapper verification

### Documentation
- Runtime parser bug root cause and rebuild limitations documented
- Duplication analysis and intentional duplications documented
- Test enablement progress tracking added

## [0.5.1-alpha] - 2026-02-09

### Added
- macOS self-hosting test automation (Intel x86_64 and Apple Silicon ARM64)
- Windows native compilation support with MSVC
- Windows cross-compilation from Linux using MinGW-w64
- FreeBSD bootstrap support via Linuxulator (experimental)
- FreeBSD QEMU testing infrastructure
- Comprehensive CI with 6 automated test jobs

### Changed
- GitHub Actions workflow expanded to 6 test jobs
- Bootstrap testing now covers 5 platforms

### Known Limitations
- Windows: Interpreter mode limited (use for compilation only)
- FreeBSD: Experimental support via Linuxulator

### Documentation
- 9 new documentation files for platform support and testing

## [0.5.0] - 2026-02-06

### Added
- 100% Pure Simple (Rust source removed)
- Self-hosting parser
- Pre-built runtime

