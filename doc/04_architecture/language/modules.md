# Architecture: Module Details

Part of [Architecture Overview](architecture.md).

## File-Based Type/Struct/Enum Listing

### common/src/

**`lib.rs`** - Core module traits and caching
- `trait DynModule` - Runtime module interface (`get_fn`, `entry_fn`)
- `trait DynLoader` - Module loader interface (`load`, `load_with_resolver`)
- `struct ModuleCache<M,E>` - Generic thread-safe caching (`get`, `insert`, `remove`, `modules`)
- `struct ModuleRegistry<L>` - Loader + cache combination (`load`, `unload`, `reload`)

**`gc.rs`** - GC contract
- `trait GcAllocator` - Memory allocation contract (`alloc_bytes`, `collect`)
- `trait GcHandle` - Marker trait for GC-managed references

**`config_env.rs`** - Configuration
- `struct ConfigEnv` - Dict-like config/env/args access

**`actor.rs`** - Actor system
- `enum Message` - Actor message types (`Value(String)`, `Bytes(Vec<u8>)`)
- `enum ActorLifecycle` - Actor state machine (`Running`, `Joined`)
- `struct ActorHandle` - Communication handle (`id`, `send`, `recv`, `join`, `is_running`)
- `trait ActorSpawner` - Spawning interface (`spawn`)
- `struct ThreadSpawner` - Thread-based spawner implementation

**`manual.rs`** - Manual memory management (matches Lean formal verification)
- `struct Nat` - Natural number newtype (matches Lean's Nat, saturating pred)
- `struct BorrowState` - Borrow tracking (`exclusive: bool`, `shared: Nat`)
- `enum ValidBorrowState` - Type-safe borrow states (`Unborrowed`, `Exclusive`, `Shared(NonZeroUsize)`)
- `struct BorrowTracker` - Thread-safe runtime borrow checker
- `struct ValidBorrowTracker` - Type-safe borrow tracker
- `struct GcState` - GC state tracking (HashSet-based, `allocate`, `borrow`, `release`, `collect_safe`)
- `struct GcStateVerify` - Vec-based GC state for Lean correspondence
- `struct GcStateTracker` - Thread-safe GC tracker
- `struct ManualGc` - Manual memory arena (`alloc`, `alloc_shared`, `alloc_handle`, `live`, `collect`)
- `struct Unique<T>` - Unique ownership pointer (`new`, `is_valid`, `into_inner`)
- `struct Shared<T>` - Reference-counted pointer (`new`, `downgrade`)
- `struct WeakPtr<T>` - Weak reference (`upgrade`)
- `struct HandlePool<T>` - Handle allocation pool (`alloc`, `resolve`, `release`)
- `struct Handle<T>` - Pool-managed handle (`resolve`)
- Pure functions: `borrow_state_valid`, `gc_state_safe`, `take_exclusive`, `take_shared`, `release_exclusive`, `release_shared`, `gc_allocate`, `gc_borrow`, `gc_release`, `gc_collect_safe`

---

### parser/src/

**`lexer.rs`** - Tokenization
- `struct Lexer<'a>` - Source → Token stream

**`token.rs`** - Token types
- `struct Span` - Source location range
- `enum FStringToken` - F-string parts
- `enum TokenKind` - Token type enum
  - **Module system tokens**: `Mod`, `Use`, `Export`, `Common`, `Auto`, `Crate`
- `struct Token` - Token with position

**`parser.rs`** - Main parser entry point
- `struct Parser<'a>` - Token stream → AST
- Delegates to submodules for parsing

**`error.rs`** - Errors
- `enum ParseError` - Parse error types

**`expressions/mod.rs`** - Expression parsing (private module)
- Pratt parser with binary operator macros (`parse_binary_single!`, `parse_binary_multi!`)
- `parse_expression()`, `parse_expression_or_assignment()`
- Expression precedence climbing implementation

**`statements/mod.rs`** - Statement parsing (private module)
- Variable declarations: `parse_let()`, `parse_mut_let()`, `parse_const()`, `parse_static()`
- Control flow: `parse_if()`, `parse_for()`, `parse_while()`, `parse_loop()`, `parse_match()`
- Jump statements: `parse_return()`, `parse_break()`, `parse_continue()`
- Module system: `parse_use()`, `parse_mod()`, `parse_common_use()`, `parse_export_use()`, `parse_auto_import()`, `parse_module_path()`, `parse_import_target()`
- Special: `parse_context()`, `parse_with()`

**`types_def/mod.rs`** - Type parsing (private module)
- `parse_type()` and related type syntax

**`ast.rs`** - AST nodes
- `enum Visibility` - Pub/private
- `enum Mutability` - Mut/immut
- `enum RangeBound` - Range bounds
- `enum SelfMode` - Self parameter modes
- `enum Node` - Top-level AST node
- **Module system**: `struct ModulePath`, `enum ImportTarget`, `struct ModDecl`, `struct UseStmt`, `struct CommonUseStmt`, `struct ExportUseStmt`, `struct AutoImportStmt`
- `struct FunctionDef`, `Parameter`, `Block`
- `struct StructDef`, `ClassDef`, `Field`
- `struct EnumDef`, `EnumVariant`
- `struct TraitDef`, `ImplBlock`, `ActorDef`
- `struct TypeAliasDef`, `ExternDef`
- `struct MacroDef`, `MacroPattern`, `MacroInvocation`
- `enum MacroParam`, `MacroBody`, `MacroToken`, `MacroArg`
- `struct LetStmt`, `ConstStmt`, `StaticStmt`
- `struct AssignmentStmt`, `enum AssignOp`
- `struct ReturnStmt`, `IfStmt`, `MatchStmt`, `MatchArm`
- `struct ForStmt`, `WhileStmt`, `LoopStmt`
- `struct BreakStmt`, `ContinueStmt`, `ContextStmt`
- `enum Type`, `PointerKind`, `Effect`
- `enum Expr`, `struct Argument`, `enum FStringPart`
- `struct LambdaParam`
- `enum BinOp`, `UnaryOp` ⚠️ *Also in hir/types.rs*
- `enum Pattern`
- `struct Module`

---

### type/src/

**`lib.rs`** - Type system
- `enum LeanTy` - Types for formal verification
- `enum LeanExpr` - Exprs for formal verification
- `enum SimpleTy` - Extended simple types
- `enum SimpleExpr` - Extended simple exprs
- `enum Type` - Full type representation
- `struct Substitution` - Type variable mapping
- `enum TypeError` - Type errors
- `struct TypeChecker` - Inference engine

---

### compiler/src/

**`error.rs`** - Errors
- `enum CompileError` - Compilation errors

**`pipeline.rs`** - Pipeline
- `struct CompilerPipeline` - Orchestration
- `with_project()`, `with_gc_and_project()` - Constructor with project context
- `compile_with_project_detection()` - Auto-detect project from file path

**`project.rs`** - Project detection and configuration
- `struct ProjectContext` - Project-level configuration holder
  - `root`, `source_root`, `name`, `resolver`, `features`, `profiles`
- `fn new(root)` - Create from project root directory
- `fn detect(file_path)` - Auto-detect project by searching for `simple.toml`
- `fn single_file(path)` - Create context for single-file mode
- `fn parse_manifest(content)` - Parse `simple.toml` content

**`module_resolver.rs`** - Module path resolution
- `struct ModuleResolver` - Resolves module paths to filesystem paths
  - `project_root`, `source_root`, `manifests`, `features`, `profiles`
- `fn resolve(path, from_file)` - Resolve module path to `ResolvedModule`
- `fn load_manifest(dir_path)` - Load and parse `__init__.spl` directory manifest
- `struct DirectoryManifest` - Parsed `__init__.spl` contents
  - `name`, `attributes`, `child_modules`, `common_uses`, `exports`, `auto_imports`
- `struct ChildModule` - Child module declaration (name, visibility, attributes)
- `struct ResolvedModule` - Resolution result (path, module_path, is_directory, manifest)

**`value.rs`** - Runtime values
- `type Env` - Variable environment
- `struct ClassName`, `EnumTypeName`, `VariantName` - Newtypes
- `enum Value` - Runtime value representation
- `struct FutureValue` - Async result
- `enum GeneratorState` - Generator lifecycle
- `struct GeneratorValue` - Coroutine state
- `struct ManualUniqueValue` - Unique wrapper
- `struct ManualSharedValue` - Shared wrapper
- `struct ManualWeakValue` - Weak wrapper
- `struct ManualHandleValue` - Handle wrapper
- `struct BorrowValue`, `BorrowMutValue` - Borrow wrappers

**`interpreter.rs`** - Interpreter entry (1364 lines)
- `enum Control` - Control flow states
- Thread-local state: ACTOR_SPAWNER, ACTOR_INBOX/OUTBOX, CONST_NAMES, etc.
- Type definitions: Enums, ImplMethods, ExternFunctions, Macros, Units
- Includes 8 modules via `include!`

**`interpreter_call.rs`** - Function call handling (532 lines)
- Call expression evaluation
- Argument evaluation and function dispatch

**`interpreter_control.rs`** - Control flow handling (522 lines)
- Block execution, if/match/loop statement execution
- Break/continue/return handling

**`interpreter_helpers.rs`** - Helper functions (559 lines)
- Common patterns extracted from expression evaluation
- Reduces duplication across interpreter modules

**`interpreter_method.rs`** - Method dispatch (357 lines)
- Built-in method handling for arrays, dicts, strings, etc.
- Method call resolution

**`interpreter_macro.rs`** - Macro expansion (315 lines)
- Macro pattern matching
- User-defined macro expansion

**`interpreter_extern.rs`** - External function handling (110 lines)
- FFI function calls

**`interpreter_context.rs`** - Context statement handling (51 lines)
- DSL support via context blocks

**`hir/types.rs`** - HIR types
- `enum Signedness` - Signed/unsigned
- `struct TypeId` - Type identifier
- `enum HirType` - HIR type representation
- `enum PointerKind` ⚠️ *Also in ast.rs*
- `struct TypeIdAllocator`, `TypeRegistry`
- `struct HirExpr`, `enum HirExprKind`
- `enum BinOp`, `UnaryOp` ⚠️ *Also in ast.rs*
- `enum HirStmt`
- `struct LocalVar`, `HirFunction`, `HirModule`

**`hir/lower.rs`** - AST→HIR
- `enum LowerError`
- `type LowerResult<T>`
- `struct Lowerer`

**`mir/types.rs`** - MIR types
- `enum LocalKind`
- `enum AsyncEffect` - Async safety effects (Compute, Io, Wait) - matches Lean `async_compile` model
- `fn is_async(e)` - Check if effect is non-blocking (Lean: `is_async`)
- `fn pipeline_safe(es)` - Check if all effects are async-safe (Lean: `pipelineSafe`)
- `enum NogcInstr` - NoGC instructions (Const, Add, GcAlloc) - matches Lean model
- `fn nogc(p)` - Check if no GC allocations
- `enum Effect` - Combined effects for production use ⚠️ *Also in ast.rs (different purpose)*
- `struct EffectSet` - Set of effects with `is_pipeline_safe()` for async safety
- `trait HasEffects` - Trait for types that report their effects
- `enum BuiltinFunc`, `CallTarget` - Known functions with effect annotations
- **Closure support**: `struct CapturedVar`, `enum CaptureMode` (ByValue, ByRef, ByMutRef)
- **Pattern matching**: `enum MirPattern`, `enum MirLiteral`, `struct PatternBinding`, `enum BindingStep`
- **F-strings**: `enum FStringPart` (Literal, Expr)

**`mir/instructions.rs`** - MIR instruction definitions
- `struct BlockId`, `VReg`
- `enum MirInst` - 50+ instruction variants (see MIR Instruction Summary below)
- `enum Terminator` - Block terminators (Return, Jump, Branch, Unreachable)

**`mir/blocks.rs`** - Basic block management
- `enum BlockBuildState`, `BlockBuildError`
- `struct BlockBuilder`, `MirBlock`

**`mir/function.rs`** - Function-level MIR
- `struct MirLocal`, `MirFunction`, `MirModule`

**`mir/effects.rs`** - Effect tracking and analysis
- Effect analysis utilities
- `CallTarget` effect annotations

**`mir/generator.rs`** - Generator state machine lowering
- `struct GeneratorState` - Per-yield state metadata
- `struct GeneratorLowering` - Lowering result
- `fn lower_generator(func, body_block)` - Rewrite generator bodies into state-machine-friendly shape

**`mir/lower.rs`** - HIR→MIR
- `struct LoopContext`
- `enum LowererState`, `BlockState`
- `enum MirLowerError`
- `type MirLowerResult<T>`
- `struct MirLowerer`

**`codegen/cranelift.rs`** - AOT code generation
- `enum CodegenError`
- `type CodegenResult<T>`
- `struct Codegen`
- Supports 50+ MIR instructions with trap fallbacks for unimplemented ops

**`codegen/jit.rs`** - JIT code generation
- JIT variant of Codegen for interactive execution
- Same instruction set as cranelift.rs
- Memory-based module loading

**`codegen/runtime_ffi.rs`** - Shared FFI function specifications
- `struct RuntimeFuncSpec` - FFI function specification (name, params, returns)
- `static RUNTIME_FUNCS: &[RuntimeFuncSpec]` - 50+ runtime function specs
- Defines all runtime function signatures (arrays, tuples, dicts, strings, values, objects, actors, generators, futures)
- Supports both AOT and JIT backends through shared spec

**`codegen/types_util.rs`** - Type conversion utilities
- `fn type_id_to_cranelift(type_id: TypeId) -> types::Type` - Map Simple types to Cranelift
- `fn type_id_size(type_id: TypeId) -> u32` - Get type size in bytes
- `fn type_to_cranelift(ty: TypeId) -> types::Type` - Alternative mapping
- Zero-cost codegen without RuntimeValue boxing

**`value_bridge.rs`** - FFI value marshalling
- `struct BridgeValue` - FFI-safe value representation (64-bit tagged)
- 23 tag constants for all value types
- Conversions: `Value ↔ BridgeValue ↔ RuntimeValue`

**`interpreter_ffi.rs`** - FFI bridge for compiled code (511 lines)
- Thread-local interpreter state (environment, functions, classes)
- `struct CompiledFnSignature` and `struct CompiledFn`
- Registry: `register_compiled_fn()`, `unregister_compiled_fn()`
- Entry points: `interp_eval_ffi()`, `interp_call_ffi()`
- `simple_interp_init(module)` - Initialize interpreter context
- `simple_interp_call(func_name, argc, argv)` - Call interpreter function
- `simple_interp_eval_expr(expr_index)` - Evaluate expression via interpreter

**`compilability.rs`** - Compilability analysis
- `enum FallbackReason` - 20+ reasons for interpreter fallback
- `enum CompilabilityStatus` - Compilable vs RequiresInterpreter
- `analyze_module()`, `analyze_function()` - Determine what can be compiled

**`linker/smf_writer.rs`** - SMF writing
- `enum DataSectionKind` - Mutable/readonly
- `enum SmfWriteError`
- `type SmfWriteResult<T>`
- `struct SmfSymbol` - Local writing struct
- `struct SmfRelocation` - Local writing struct
- `struct SmfSection` - Local writing struct
- `struct SmfWriter`
- Re-exports from `loader/smf/`: `SectionType`, `SymbolBinding`, `SymbolType`, `RelocationType`

---

### loader/src/

**`loader.rs`** - SMF loading
- `struct ModuleLoader`
  - `load(path)` - Load SMF from file
  - `load_with_resolver(path, F)` - Load with custom symbol resolver
  - `load_from_memory(bytes)` - Load SMF from memory buffer (TODO)
  - `load_from_memory_with_resolver(bytes, F)` - Load from memory with resolver (TODO)
- `enum LoadError`

**`module.rs`** - Loaded module
- `struct LoadedModule`

**`registry.rs`** - Module registry
- `type ModuleRegistryBase`
- `struct ModuleRegistry`

**`smf/header.rs`** - SMF header (CANONICAL)
- `struct SmfHeader`
- `enum Platform`, `Arch`

**`smf/section.rs`** - Sections (CANONICAL)
- `struct SmfSection`
- `enum SectionType`

**`smf/symbol.rs`** - Symbols (CANONICAL)
- `struct SmfSymbol`
- `enum SymbolType`, `SymbolBinding`
- `struct SymbolTable`

**`smf/reloc.rs`** - Relocations (CANONICAL)
- `struct SmfRelocation`
- `enum RelocationType`

**`memory/mod.rs`** - Memory abstraction
- `type PlatformAllocator`
- `enum Protection`
- `struct ExecutableMemory`
- `trait MemoryAllocator`

**`memory/posix.rs`** - POSIX impl
- `struct PosixAllocator`

**`memory/windows.rs`** - Windows impl
- `struct WindowsAllocator`

---

### native_loader/src/

**`loader.rs`** - Native loading
- `struct ModuleLoader`
- `enum LoadError`

**`module.rs`** - Loaded module
- `struct LoadedModule`

**`registry.rs`** - Registry
- `type ModuleRegistry`

---

### runtime/src/

**`lib.rs`** - Re-exports
- Re-exports `memory::gc`, `NoGcAllocator`
- Re-exports `RuntimeValue` types and 50+ FFI functions

**`value/mod.rs`** - Runtime value system (9 modules)
- Aggregates all value types and FFI functions
- Comprehensive re-export lists

**`value/core.rs`** - Core RuntimeValue
- `struct RuntimeValue(u64)` - 64-bit tagged pointer
- Methods: `is_int()`, `as_int()`, `from_int()`, etc.

**`value/tags.rs`** - Tag constants
- `TAG_INT`, `TAG_HEAP`, `TAG_FLOAT`, `TAG_SPECIAL`

**`value/heap.rs`** - Heap header management
- `struct HeapHeader` - Common header for heap objects
- `enum HeapObjectType` - String, Array, Dict, Tuple, Object, Closure, Enum, Future, Generator, Actor, Unique, Shared, Borrow

**`value/collections.rs`** - Collection types + FFI
- `struct RuntimeArray`, `RuntimeTuple`, `RuntimeDict`, `RuntimeString`
- **FFI functions**:
  - Array ops: `rt_array_new`, `rt_array_push`, `rt_array_get`, `rt_array_set`, `rt_array_pop`, `rt_array_clear`
  - Tuple ops: `rt_tuple_new`, `rt_tuple_set`, `rt_tuple_get`, `rt_tuple_len`
  - Dict ops: `rt_dict_new`, `rt_dict_set`, `rt_dict_get`, `rt_dict_len`, `rt_dict_clear`, `rt_dict_keys`, `rt_dict_values`
  - String ops: `rt_string_new`, `rt_string_concat`, `rt_string_data`, `rt_string_len`

**`value/objects.rs`** - Object/Closure/Enum types + FFI
- `struct RuntimeObject` - Class/struct instance
- `struct RuntimeClosure` - Closure with captured values
- `struct RuntimeEnum` - Enum variant with payload
- **FFI functions**:
  - Object ops: `rt_object_new`, `rt_object_field_get`, `rt_object_field_set`, `rt_object_class_id`, `rt_object_field_count`
  - Closure ops: `rt_closure_new`, `rt_closure_set_capture`, `rt_closure_get_capture`, `rt_closure_func_ptr`
  - Enum ops: `rt_enum_new`, `rt_enum_discriminant`, `rt_enum_payload`

**`value/ffi.rs`** - Value conversion and core FFI
- Memory: `rt_alloc`, `rt_free`, `rt_ptr_to_value`
- Values: `rt_value_int`, `rt_value_float`, `rt_value_bool`, `rt_value_nil`
- Extraction: `rt_value_as_int`, `rt_value_as_float`, `rt_value_as_bool`
- Checking: `rt_value_eq`, `rt_value_truthy`
- Fallback: `rt_interp_call`, `rt_interp_eval`

**`value/actors.rs`** - Actor FFI
- `struct RuntimeActor`
- **FFI functions**: `rt_actor_spawn`, `rt_actor_send`, `rt_actor_recv`
- Thread-local actor mailbox state

**`value/async_gen.rs`** - Future and Generator FFI
- `struct RuntimeFuture`, `struct RuntimeGenerator`
- **FFI functions**:
  - Future: `rt_future_new`, `rt_future_await`
  - Generator: `rt_generator_new`, `rt_generator_next`, `rt_generator_get_state`, `rt_generator_set_state`
  - Frame save/restore: `rt_generator_load_slot`, `rt_generator_store_slot`, `rt_generator_mark_done`, `rt_generator_get_ctx`

**`memory/gc.rs`** - GC runtime
- `enum GcLogEventKind`
- `struct GcLogEvent`
- `struct GcRuntime` - Abfall-backed GC wrapper with logging

**`memory/no_gc.rs`** - No-GC allocator
- `struct NoGcAllocator` - GC-off profile implementation

**`concurrency/mod.rs`** - Actor scheduler
- `struct Scheduler` (private) - Global actor registry with mailboxes and join handles
- `struct ScheduledSpawner` - Actor spawner that registers with global scheduler
- `fn spawn_actor<F>` - Spawn a new actor thread with mailbox setup
- `fn send_to(id, msg)` - Send message to actor by ID (scheduler dispatch)
- `fn join_actor(id)` - Join an actor by ID (scheduler join table)

---

### pkg/src/ (Package Manager)

**`lib.rs`** - Package manager entry
- Re-exports all public types and commands

**`manifest.rs`** - Manifest parsing
- `struct Manifest` - simple.toml representation
- `struct Dependency` - Dependency specification (path, git, version)

**`lock.rs`** - Lock file format
- `struct LockFile` - simple.lock representation
- `struct LockedDependency` - Resolved dependency with exact version

**`cache.rs`** - Global cache
- `struct Cache` - Global package cache with hard links
- Methods: `get()`, `put()`, `list()`, `clean()`

**`version.rs`** - Version handling
- `struct Version` - Semantic version
- `struct VersionReq` - Version requirement/constraint

**`error.rs`** - Error types
- `enum PkgError` - Package manager errors
- `type PkgResult<T>` - Result alias

**`linker.rs`** - Dependency linking
- `struct Linker` - Links dependencies into project

**`resolver/mod.rs`** - Dependency resolution
- `struct Resolver` - Dependency resolver

**`resolver/graph.rs`** - Dependency graph
- `struct DepGraph` - Dependency graph with topological ordering
- `fn topological_sort()` - Build order computation

**`commands/mod.rs`** - CLI command entry
- Re-exports all command handlers

**`commands/init.rs`** - Project initialization
- `fn init()` - Create new simple.toml

**`commands/install.rs`** - Dependency installation
- `fn install()` - Install all dependencies from lock file

**`commands/add.rs`** - Add dependency
- `fn add(name, version)` - Add dependency to manifest

**`commands/update.rs`** - Update dependencies
- `fn update()` - Update dependencies to latest compatible versions

**`commands/list.rs`** - List dependencies
- `fn list()` - Show dependency tree

**`commands/cache_cmd.rs`** - Cache management
- `fn cache_list()`, `fn cache_clean()` - Cache operations

---

### util/simple_mock_helper/src/

**`lib.rs`** - Re-exports all public items

**`api_scanner.rs`** - Public API scanning
- `struct ScannedApi` - Scanned API data
- `struct ScannedType` - Scanned type information
- `fn scan_directory` - Scan directory for public APIs
- `fn generate_yaml` - Generate YAML from scanned APIs
- `fn write_yaml` - Write YAML to file
- `fn merge_with_existing` - Merge with existing API spec

**`coverage.rs`** - Coverage analysis
- `struct ClassCoverage` - Class-level coverage data
- `struct MethodCoverage` - Method-level coverage data
- `struct CoverageSummary` - Overall coverage summary
- `struct PublicApiSpec` - Public API specification
- `struct LlvmCovExport` - LLVM coverage export data
- `fn compute_class_coverage` - Compute class coverage from llvm-cov
- `fn load_llvm_cov_export` - Load llvm-cov export file
- `fn load_public_api_spec` - Load public API spec from YAML
- `fn print_class_coverage_table` - Print coverage table

**`mock_policy.rs`** - Mock control for tests
- `enum MockCheckResult` - Result of mock permission check
- `const DEFAULT_HAL_PATTERNS` - Default HAL mock patterns
- `const DEFAULT_ENV_PATTERNS` - Default environment mock patterns
- `fn are_mocks_enabled` - Check if mocks are enabled
- `fn check_mock_use_from` - Check if mock use is allowed
- `fn try_check_mock_use_from` - Try to check mock permission
- `fn get_allowed_patterns` - Get allowed mock patterns
- `fn init_mocks_for_only` - Initialize mocks for specific patterns
- `fn init_mocks_for_only_default` - Initialize with default patterns
- `fn init_mocks_for_system` - Initialize for system tests (no mocks)
- `fn is_policy_initialized` - Check if policy is initialized

**`test_check.rs`** - Test level management
- `enum TestLevel` - Test level (`Unit`, `Integration`, `System`, `Environment`)
- `struct TestCheckResult` - Result of test check
- `fn get_test_level` - Get current test level
- `fn get_test_level_name` - Get test level name
- `fn try_get_test_level` - Try to get test level
- `fn init_test_level` - Initialize test level
- `fn init_test_level_named` - Initialize test level with name
- `fn assert_test_level` - Assert expected test level
- `fn assert_mocks_allowed` - Assert mocks are allowed
- `fn assert_mocks_forbidden` - Assert mocks are forbidden
- `fn validate_test_config` - Validate test configuration

---

### driver/src/

**`lib.rs`** - Re-exports
- Re-exports `Runner`, `watch`, `run_code`, `Interpreter`, `RunResult`, `RunConfig`

**`exec_core.rs`** - Low-level execution engine (shared logic)
- `struct ExecCore`
  - `loader: SmfLoader` - SMF module loader
  - `gc_alloc: Arc<dyn GcAllocator>` - GC allocator trait object
  - `gc_runtime: Option<Arc<GcRuntime>>` - Optional GC runtime for logging
  - `new()`, `new_no_gc()` - Create with/without GC
  - `compile_source(source, out)` - Compile source to SMF file
  - `compile_file(path, out)` - Compile file to SMF
  - `compile_to_memory(source)` - Compile to bytes, no disk I/O
  - `compile_to_memory_native(source)` - Compile to native code in memory
  - `load_module(path)` - Load SMF from file
  - `load_module_from_memory(bytes)` - Load SMF from memory
  - `run_smf(path)` - Run pre-compiled SMF file
  - `run_smf_from_memory(bytes)` - Run SMF from memory
  - `run_source(source)` - Compile and run (uses temp file)
  - `run_source_in_memory(source)` - Compile and run, no disk I/O
  - `run_file(path)` - Auto-detect .spl/.smf and run
  - `execute()` - Execute loaded module
  - `collect_gc()` - Trigger GC collection

**`runner.rs`** - Mid-level public API
- `struct Runner`
  - `new()`, `new_no_gc()` - Create with/without GC
  - `run_source(source)` - Compile and run source string
  - `run_source_in_memory(source)` - Compile and run without disk I/O
  - `run_file(path)` - Run .spl or .smf file (auto-detect)
  - `run_smf(path)` - Run pre-compiled SMF directly
  - `compile_to_smf(source, out)` - Compile source to SMF file
  - `gc_runtime()` - Access underlying GC runtime

**`interpreter.rs`** - High-level API with I/O capture
- `struct Interpreter`
  - `new()`, `new_no_gc()` - Create with/without GC
  - Uses `Runner` internally (delegates execution)
  - `run(code, config)` - Run with configuration
  - `run_with_stdin(code, stdin)` - Run with stdin input
  - `run_simple(code)` - Run without config
  - `run_in_memory(code)` - Run without disk I/O
  - `runner()` - Access underlying Runner
  - `gc()` - Access underlying GC runtime
- `struct RunResult` - `exit_code`, `stdout`, `stderr`
- `struct RunConfig` - `args`, `stdin`, `timeout_ms`, `in_memory`
- `fn run_code(code, args, stdin)` - Convenience function for running code

**`dependency_cache.rs`** - Import/macro dependency tracking
- `struct DepInfo` - Dependency information
- `struct BuildCache` - Build cache for incremental compilation

**`watcher/mod.rs`** - File watching
- `fn watch(path, callback)` - Watch file for changes and trigger rebuild

---


---

Next: [Data Flow and Execution](architecture_flows.md)
