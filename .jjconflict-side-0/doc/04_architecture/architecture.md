# Architecture Overview

The Simple language is a self-hosted compiler written in Simple itself. The bootstrap chain starts from a Rust seed compiler, which compiles the Simple compiler, which then compiles itself (3-stage bootstrap verification).

## Compiler Pipeline

The compiler is organized as numbered layers in `src/compiler/`:

| Layer | Name | Responsibility |
|-------|------|---------------|
| 00 | Common | Error types, config, effects, visibility, diagnostics, DI, SIMD type definitions |
| 10 | Frontend | Lexer, parser, AST, tokens, treesitter, desugar |
| 15 | Blocks | Block definition system |
| 20 | HIR | HIR types, definitions, lowering, inference (fully resolved in stage-4 bootstrap) |
| 25 | Traits | Trait def, impl, solver, coherence, validation |
| 30 | Types | Type system, SIMD types, capabilities, platform types |
| 35 | Semantics | Semantic analysis, lint, SIMD checks |
| 40 | Mono | Monomorphization |
| 50 | MIR | MIR instructions (includes masked/predicated SIMD opcodes) |
| 55 | Borrow | Borrow checking |
| 60 | MIR Opt | MIR optimization passes (SIMD lowering, predicate promotion) |
| 70 | Backend | Native code generation (Cranelift AOT, x86_64 SIMD) |
| 80 | Driver | Pipeline orchestrator |
| 85 | MDSOC | MDSOC capsule analysis |
| 90 | Tools | Lint, fix, formatting, diagnostics |
| 95 | Interp | Interpreter |
| 99 | Loader | Module loader, entry point |

## Library Structure

Standard library lives in `src/lib/`, organized by mutability and GC requirements:

| Directory | Import | Purpose |
|-----------|--------|---------|
| `common/` | `use std.*` | Pure functions: text, math, json, crypto, encoding, UI framework |
| `nogc_sync_mut/` | `use std.*` | Sync mutable: FFI, FS, net, HTTP, database, MCP, spec, SIMD, ECS |
| `nogc_async_mut/` | `use std.*` | Async mutable: actors, async, threads, generators |
| `gc_async_mut/` | `use std.*` | GC + async: GPU, CUDA, torch, ML, Engine2D, browser engine |
| `nogc_async_mut_noalloc/` | `use std.*` | Baremetal: execution, memory, QEMU |

Additional library modules: `blink/`, `cc/`, `content/`, `skia/`, `viz/`, `scipy/`, `sdn/`, `gui/`, `lint/`, `log/`, `ffi/`, `async/`, `database/`.

## SimpleOS Structure

SimpleOS is a MDSOC-based microkernel OS in `src/os/`:

| Directory | Purpose |
|-----------|---------|
| `kernel/` | Microkernel: capability security, syscalls, scheduling |
| `compositor/` | Window compositor with Engine2D backend |
| `desktop/` | Desktop shell, app launcher, taskbar, app manifests |
| `apps/` | 29 desktop applications (calculator, editor, terminal, browser, games, etc.) |
| `services/` | Userland services: WM, display server, render service |
| `drivers/` | Device drivers: framebuffer, input, storage, network |
| `gui/` | GUI subsystem |
| `libc/` | libc / POSIX shim layer |
| `posix/` / `sosix/` | POSIX compatibility |
| `runtime/` | OS runtime support |
| `sdk/` | SDK for app development |
| `tools/` | OS development tools |
| `tls12/` / `tls13/` / `crypto/` | TLS and cryptographic subsystems |
| `packages/` / `installer/` | Package management |

All 29 desktop apps and the shell use the UISession + widget builder DSL pattern. See [SimpleOS Desktop Architecture](simpleos_desktop_architecture.md).

## Browser Engine

A Chromium-class browser engine in `src/lib/gc_async_mut/gpu/browser_engine/`:

- **DOM** (`dom.spl`) -- DOM tree construction and manipulation
- **CSS** (`css.spl`, `style_block.spl`) -- CSS parsing, variable resolution, float layout
- **Layout** (`layout.spl`) -- Box model, float positioning, block/inline flow
- **Paint** (`paint.spl`) -- Paint operations, visibility, compositing
- **Renderer** (`browser_renderer.spl`) -- Pipeline orchestrator: HTML -> DOM -> style -> layout -> paint -> pixels
- **Glass comparison** (`glass_comparison_runner.spl`, `glass_pipeline_compare.spl`) -- Pixel-accurate rendering comparison

## SIMD AOT Pipeline

SIMD support spans the full compiler pipeline. See [SIMD AOT Architecture](simd_aot_architecture.md).

## Bootstrap Pipeline

Three-stage self-compilation verification:

1. **Stage 1** -- Rust seed compiler (`src/compiler_rust/`) compiles the Simple compiler
2. **Stage 2** -- Stage-1 output compiles the Simple compiler again
3. **Stage 3** -- Stage-2 output compiles the Simple compiler; binary-compare with Stage 2

Commands: `bin/simple build` (debug), `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (full bootstrap).

## Architecture Pattern: MDSOC+

Default architecture is MDSOC+ (MDSOC outer + ECS business layer for userland; kernel/drivers stay MDSOC-only). See [MDSOC Architecture](mdsoc_architecture_tobe.md).

## Detailed References

- [Overview](overview.md)
- [Modules](modules.md)
- [Flows](flows.md)
- [Dev](dev.md)
- [Support](support.md)
- [MDSOC Architecture](mdsoc_architecture_tobe.md)
- [SimpleOS Desktop Architecture](simpleos_desktop_architecture.md)
- [SIMD AOT Architecture](simd_aot_architecture.md)
- [File/Class Structure](file_class_structure.md)
- [Glossary](glossary.md)
