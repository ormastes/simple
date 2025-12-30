//! Linker module for Simple language.
//!
//! This module provides:
//! - **SMF Writer**: Creates Simple Module Format binaries
//! - **Native Linker**: High-performance native linking with mold/lld/ld support
//! - **Parallel Linker**: Parallel SMF linking using rayon
//! - **Layout Optimizer**: 4KB page locality optimization (#2030-#2039)
//!
//! # Native Linker Selection
//!
//! The native linker is auto-detected in order of preference:
//! 1. **Mold** (Linux only): Fastest linker, ~4x faster than lld
//! 2. **LLD**: LLVM's linker, cross-platform, fast
//! 3. **GNU ld**: Traditional fallback
//!
//! Override with `SIMPLE_LINKER` environment variable or `--linker` CLI flag.

pub mod analysis;
mod smf_writer;
mod error;
mod interner;
mod native;
mod builder;
pub mod parallel;
pub mod layout;
mod native_binary;

// SMF exports
pub use smf_writer::*;

// Native linker exports
pub use error::{LinkerError, LinkerResult};
pub use native::{LinkOptions, NativeLinker};
pub use builder::{link_objects, link_with, LinkerBuilder};

// Symbol interning exports
pub use interner::{
    CommonSymbols, InternedSymbolTable, SharedSymbolInterner, SymbolBinding as InternedSymbolBinding,
    SymbolInfo, SymbolInterner, SymbolKey, SymbolType as InternedSymbolType,
};

// Parallel linking exports
pub use parallel::{
    link_modules_parallel, link_modules_parallel_with_config, BatchLinker, LinkModule, LinkStats,
    ParallelLinkConfig, ParallelLinker, ParallelSymbolTable, SymbolEntry,
};

// Symbol analysis exports
pub use analysis::{
    AnalysisStats, AnalyzedSymbol, RefKind, SymbolAnalyzer, SymbolGraph, SymbolVisibility,
};

// Layout optimization exports (4KB page locality)
pub use layout::{
    LayoutOptimizer, LayoutSegment, LayoutStats, LayoutSymbol,
};

// Native binary exports (standalone executables)
pub use native_binary::{
    compile_to_native_binary, NativeBinaryBuilder, NativeBinaryOptions, NativeBinaryResult,
};
