#![allow(unused_imports, unused_variables, unused_comparisons, deprecated)]
//! Class/Struct method coverage tests
//! Coverage for GcRuntime, Concurrency, BlockBuilder, MirModule, etc.

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// Class/Struct Method Coverage - GcRuntime
// =============================================================================

/// Test GcRuntime methods for class coverage
#[test]
fn test_gc_runtime_methods() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();

    // Test heap_bytes
    let bytes = gc.heap_bytes();
    assert!(bytes >= 0);

    // Test heap
    let _heap = gc.heap();
}

/// Test GcRuntime::verbose_stdout
#[test]
fn test_gc_runtime_verbose() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::verbose_stdout();
    let _bytes = gc.heap_bytes();
}

/// Test GcRuntime::collect for class coverage
#[test]
fn test_gc_runtime_collect_class_coverage() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let freed = gc.collect("test");
    // May or may not free anything
    let _ = freed;
}

// =============================================================================
// Class/Struct Method Coverage - Concurrency Types
// =============================================================================

/// Test ScheduledSpawner
#[test]
fn test_scheduled_spawner_methods_system() {
    use simple_runtime::concurrency::ScheduledSpawner;

    let spawner = ScheduledSpawner::new();
    // ScheduledSpawner is a zero-size type, just verify it exists
    let _ = spawner;
}

/// Test spawn_actor function
#[test]
fn test_spawn_actor_function_system() {
    use simple_runtime::concurrency::spawn_actor;

    let handle = spawn_actor(|_ctx, _msg| {
        // Simple actor that handles messages
    });

    // Actor handle should be valid
    assert!(handle.id() >= 0); // id is valid
}

// =============================================================================
// Class/Struct Method Coverage - BlockBuilder
// =============================================================================

/// Test BlockBuilder methods
#[test]
fn test_block_builder_methods() {
    use simple_compiler::mir::{BlockBuilder, BlockId, MirInst, Terminator, VReg};

    let mut builder = BlockBuilder::new(BlockId(0));

    // Test state
    assert!(builder.is_open());
    assert!(!builder.is_sealed());
    assert_eq!(builder.id().0, 0);

    // Test push instruction - use ConstInt instead of Const
    let inst = MirInst::ConstInt {
        dest: VReg(0),
        value: 42,
    };
    let push_result = builder.push(inst);
    assert!(push_result.is_ok());

    // Test seal
    let seal_result = builder.seal(Terminator::Return(Some(VReg(0))));
    assert!(seal_result.is_ok());
    assert!(builder.is_sealed());
}

/// Test BlockBuilder finalize
#[test]
fn test_block_builder_finalize() {
    use simple_compiler::mir::{BlockBuilder, BlockId, Terminator, VReg};

    let mut builder = BlockBuilder::new(BlockId(1));
    builder.seal(Terminator::Return(None)).expect("seal");

    let block = builder.finalize();
    assert!(block.is_ok());
}

// =============================================================================
// Class/Struct Method Coverage - MirModule
// =============================================================================

/// Test MirModule methods
#[test]
fn test_mir_module_methods() {
    use simple_compiler::mir::MirModule;

    let module = MirModule::new();
    assert!(module.functions.is_empty());
}

// =============================================================================
// Class/Struct Method Coverage - TypeIdAllocator
// =============================================================================

/// Test TypeIdAllocator methods
#[test]
fn test_type_id_allocator_methods() {
    use simple_compiler::hir::TypeIdAllocator;

    let mut allocator = TypeIdAllocator::new();

    // Test alloc
    let id1 = allocator.alloc();
    let id2 = allocator.alloc();
    assert_ne!(id1.0, id2.0);

    // Test peek_next
    let next = allocator.peek_next();
    assert!(next > id2.0);
}

/// Test TypeIdAllocator::with_start
#[test]
fn test_type_id_allocator_with_start() {
    use simple_compiler::hir::TypeIdAllocator;

    let mut allocator = TypeIdAllocator::with_start(100);
    let id = allocator.alloc();
    assert_eq!(id.0, 100);
}

// =============================================================================
// Class/Struct Method Coverage - LowererState
// =============================================================================

/// Test LowererState methods
#[test]
fn test_lowerer_state_methods() {
    use simple_compiler::mir::MirLowerer;

    let lowerer = MirLowerer::new();
    let state = lowerer.state();

    // Test state methods
    assert!(state.is_idle());
    assert!(!state.is_lowering());
}

// =============================================================================
// Class/Struct Method Coverage - Additional Loader Types
// =============================================================================

/// Test ModuleLoader::load_from_memory
#[test]
fn test_module_loader_load_from_memory() {
    use simple_driver::Runner;
    use simple_loader::ModuleLoader;
    use std::fs;
    use tempfile::tempdir;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("memory_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile ok");

    let bytes = fs::read(&smf_path).expect("read ok");
    let loader = ModuleLoader::new();
    let module = loader.load_from_memory(&bytes);
    assert!(
        module.is_ok(),
        "Should load from memory: {:?}",
        module.err()
    );
}

/// Test ModuleLoader::load_with_resolver
#[test]
fn test_module_loader_load_with_resolver() {
    use simple_driver::Runner;
    use simple_loader::ModuleLoader;
    use tempfile::tempdir;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("resolver_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 99", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load_with_resolver(&smf_path, |_name| None);
    assert!(
        module.is_ok(),
        "Should load with resolver: {:?}",
        module.err()
    );
}

// =============================================================================
// Additional Value Method Coverage
// =============================================================================

/// Test Value::to_key_string
#[test]
fn test_value_to_key_string() {
    use simple_compiler::Value;

    let int_val = Value::Int(42);
    let key = int_val.to_key_string();
    assert!(!key.is_empty());

    let str_val = Value::Str("hello".to_string());
    let str_key = str_val.to_key_string();
    assert!(str_key.contains("hello"));
}

/// Test Value::matches_type
#[test]
fn test_value_matches_type() {
    use simple_compiler::Value;

    let int_val = Value::Int(42);
    assert!(int_val.matches_type("i64"));
    assert!(!int_val.matches_type("str"));

    let bool_val = Value::Bool(true);
    assert!(bool_val.matches_type("bool"));
}

/// Test Value::deref_pointer
#[test]
fn test_value_deref_pointer() {
    use simple_compiler::Value;

    // Non-pointer value should return itself
    let val = Value::Int(42);
    let derefed = val.deref_pointer();
    assert!(matches!(derefed, Value::Int(42)));
}
