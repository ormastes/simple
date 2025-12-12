# Todo

## dirctory __init__.spl
DONE - Full implementation in module_resolver.rs with 21 __init__.spl files in stdlib

## api doc gen
### DONE: Block comments and doc comment tokens
- Block comments /* */ implemented in lexer
- Doc comments /** */ and ## implemented in lexer (emit DocComment tokens)
- DocComment struct added to AST (simplified: just content string)
- doc_comment field added to FunctionDef, StructDef, ClassDef, EnumDef, TraitDef
- Parser attaches doc comments to following definitions

### Design: Simple doc comment approach
- Doc comments are used directly as API descriptions (no @param/@returns tags)
- Parameter names should be descriptive (self-documenting code)
- Inline comments can be added to params and return types in code
- Example: `fn calculate_total_price(item_count: Int, unit_price: Float) -> Float`

### DONE: API doc generation
- Created `src/parser/src/doc_gen.rs` module
- `generate(&Module) -> ModuleDocs` extracts documented items
- `ModuleDocs::to_markdown()` generates Markdown documentation
- `ModuleDocs::to_html()` generates HTML documentation with CSS styling
- Supports: functions, structs, classes, enums, traits
- Groups items by kind with proper signatures

## excessive error and warning messages
### DONE: Rust-style diagnostics system
- Created `src/parser/src/diagnostic.rs` with full diagnostic support
- Features:
  - `Diagnostic` struct with severity (Error, Warning, Note, Help)
  - Error codes (E0001-E0012)
  - Source code context with line numbers
  - Colored output (red=error, yellow=warning, cyan=note, green=help)
  - Underline markers (^^^ for primary, --- for secondary)
  - Labels, notes, and help suggestions
  - `Diagnostics` collection for multiple errors
- Updated `ParseError` with:
  - New error variants (MissingToken, InvalidPattern, InvalidType, etc.)
  - `to_diagnostic()` method for rich error formatting
  - `format_with_source()` for formatted output with source context
  - Span information for all errors

### DONE: Compiler diagnostic integration
- Extended `src/compiler/src/error.rs` with rich diagnostic support:
  - `ErrorContext` struct with span, file, code, notes, help fields
  - Error codes module (`error::codes`) with E1xxx (semantic), E2xxx (codegen), E3xxx (runtime)
  - `CompileError::to_diagnostic()` converts to parser's `Diagnostic` type
  - `CompileError::format_with_source()` for formatted output with source context
  - Helper methods: `semantic_with_context()`, `runtime_with_context()`, etc.
  - Backward compatible with existing `CompileError::Semantic(String)` pattern
  - Macros `semantic_error!` and `runtime_error!` for ergonomic error creation

### DONE: Typo detection and suggestions
- Added `error::typo` module with:
  - `levenshtein_distance()` for string similarity calculation
  - `find_similar()` to find names within edit distance threshold
  - `suggest_name()` with dynamic threshold based on name length (1-3 chars: 1 edit, 4-6: 2, 7+: 3)
  - `format_suggestion()` to format "did you mean 'foo'?" messages
- Integrated typo suggestions into error messages for:
  - Undefined variables (in `interpreter_expr.rs`, `interpreter.rs`, `interpreter_helpers.rs`)
  - Unknown methods on objects, Future, Channel, ThreadPool
  - Unknown static methods on classes
  - Unknown class names

### DONE: Multi-file error tracking
- Added `SourceRegistry` in `src/parser/src/diagnostic.rs`:
  - `add(path, source)` to register source files
  - `get(path)` to retrieve source code
  - `contains(path)` to check if file exists
  - `files()` to iterate file paths
- Extended `Diagnostics` with multi-file support:
  - `format_multi_file(sources, use_color)` formats diagnostics using per-file sources
  - `by_file()` groups diagnostics by their file path
  - `for_file(path)` filters diagnostics for a specific file
## structured logging
DONE - Structured logging modules in log/ crate:
- log/src/parse/mod.rs - Compile-time logging (lexer, parser, module resolution)
  - token(), lex_error(), lex_warning(), lex_phase()
  - ast_node(), parse_error(), parse_warning(), parse_rule(), parse_recovery()
  - module_resolve(), import_process()
  - Span functions: lex_file_span(), parse_file_span(), parse_construct_span()
- log/src/run_time/mod.rs - Runtime logging (execution, GC, actors, async, I/O)
  - call(), ret(), block_enter(), block_exit(), runtime_error(), panic()
  - alloc(), dealloc(), gc_start(), gc_end(), gc_mark(), gc_sweep(), heap_stats()
  - actor_spawn(), actor_terminate(), actor_send(), actor_recv()
  - async_spawn(), async_complete(), await_start(), await_end()
  - file_open/close/read/write(), net_connect/disconnect(), io_error()
  - value_create(), value_convert(), method_dispatch()
  - Span functions: call_span(), gc_span(), actor_span(), async_span()
- Initialized via simple_log::init() in driver/src/main.rs
- Controlled by SIMPLE_LOG or RUST_LOG env vars

## std lib
DONE - Extensive traits in lib/std/core/traits.spl (Default, Clone, Copy, Eq, Ord, Hash, Display, Debug, From, Into) with implementations across String, List, collections.

## ruby python like easy api
DONE - Ruby/Python-style chainable methods in lib/std/core/list.spl:
- Ruby-style: select, reject, partition, compact, flatten, tap, then
- Python-style: chunks, windows
- Chainable: map_with_index, join, dedup
- Functional: filter, map, take, drop, take_while, drop_while
## compile type inference
DONE - Monomorphization engine implemented in src/compiler/src/monomorphize.rs:
- SpecializationKey and ConcreteType for type representation
- MonomorphizationTable tracks pending and completed specializations
- Monomorphizer generates specialized versions of generic functions/structs/classes
- CallSiteAnalyzer collects generic function calls and infers type arguments
- monomorphize_module() convenience function for full module processing
- Integrated into CompilerPipeline (both interpreter and native modes)
- Features:
  - Name mangling (identity[Int] -> identity$Int)
  - Type substitution in function bodies
  - Recursive specialization discovery
  - Support for structs, classes, and functions

## smf loading improvement
### DONE: Settlement and AOT executable generation
- Settlement container for managing multiple modules with shared memory regions
- Function/global/type tables with indirection for hot reload support
- SettlementBuilder serializes to SSMF (Simple Settlement Module Format)
- StartupLoader loads settlement data from executables
- simple-stub crate provides minimal executable entry point
- AOT executable pipeline: Source → SMF → Settlement → Executable
- Relative offset conversion for position-independent code
- RunningType::All mode tests interpreter + JIT + AOT together

### TODO: Advanced SMF features
- Link multiple SMF modules together
- Manage references (shared logic with build reference management)
- SMF swap with new SMF (hot code replacement)
- Remove SMF from settlement dynamically
- Reference: Java class loader, Erlang hot code replacement


## packaging
DONE (basic) - UV-style package manager implemented in src/pkg/:
- simple.toml manifest parsing
- simple.lock lock file for reproducible builds
- Path and Git dependencies
- Global cache with hard links
- Dependency resolution with topological ordering

### TODO: Advanced packaging
- Modified zip package with header on tail
- Executable at front without compression
- Config files (package, lock) not compressed

## gpu (cuda) support
DONE (stdlib) - GPU stdlib exists in lib/std/gpu/:
- lib/std/gpu/kernel/ - Device-side (single: async+nogc+immut)
- lib/std/gpu/host/async_nogc_mut/ - Host-side GPU control (device, buffer, kernel, stream)

### TODO: GPU implementation
- How to efficiently express GPU operations
- Share operations between threads
- Less efficient branch handling
- Bank separation

## embedded support
DONE (stdlib) - Bare metal stdlib exists in lib/std/bare/:
- hal/ - Hardware abstraction layer
- io/ - I/O operations
- async/ - Async primitives

### TODO: Embedded implementation
- Startup code for embedded system
- Teardown bin from settlement SMF
- Float-less, OS alloc-less, thread-less, GC-less variants

## Multi-architecture support
### TODO: Additional architecture targets
**32-bit targets:**
- x86 (i686)
- ARM (armv7)
- RISC-V 32 (riscv32)

**64-bit targets (beyond x86_64):**
- ARM64 (aarch64)
- RISC-V 64 (riscv64)

**Implementation tasks:**
- Cranelift codegen backend for each target
- Pointer size handling (usize/isize as 4 bytes on 32-bit)
- Runtime value representation for 32-bit (currently uses 64-bit tagged pointers)
- SMF format compatibility (32-bit vs 64-bit sections)
- Settlement loader for each architecture
- Executable stub for each target
- Test infrastructure for cross-compilation
- CI/CD for multi-architecture builds
