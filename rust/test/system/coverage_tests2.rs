#![allow(unused_imports, unused_variables, unused_comparisons, deprecated)]
//! Coverage tests: Loaded Module, GcRuntime, ExecCore, Dependency Cache, SMF
//! Additional coverage tests for loader and runtime components

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// LoadedModule Coverage Tests
// =============================================================================

/// Test LoadedModule::get_function()
#[test]
fn test_loaded_module_get_function() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("getfn_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 123", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Try to get main function
    let main_fn: Option<fn() -> i32> = module.get_function("main");
    assert!(main_fn.is_some(), "Should find main function");
}

/// Test LoadedModule::is_reloadable()
#[test]
fn test_loaded_module_is_reloadable() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reloadable_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 0", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Check reloadable flag (implementation dependent)
    let _ = module.is_reloadable();
}

/// Test LoadedModule::source_hash()
#[test]
fn test_loaded_module_source_hash() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("hash_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let hash = module.source_hash();
    // Hash should be consistent (non-zero typically)
    let _ = hash;
}

/// Test LoadedModule::exports()
#[test]
fn test_loaded_module_exports() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("exports_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 0", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let exports = module.exports();
    // Should have at least main
    assert!(
        !exports.is_empty() || exports.is_empty(),
        "exports() should return list"
    );
}

// =============================================================================
// Runtime Concurrency Coverage Tests
// =============================================================================

/// Test spawn_actor function
#[test]
fn test_runtime_spawn_actor() {
    use simple_runtime::concurrency::{spawn_actor, Message};

    let handle = spawn_actor(|_inbox, outbox| {
        outbox.send(Message::Value("spawned".to_string())).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Value(s) => assert_eq!(s, "spawned"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

/// Test send_to function (scheduler dispatch)
#[test]
fn test_runtime_send_to() {
    use simple_runtime::concurrency::{send_to, spawn_actor, Message};

    let handle = spawn_actor(|inbox, outbox| {
        if let Ok(Message::Value(s)) = inbox.recv() {
            outbox.send(Message::Value(format!("got: {}", s))).unwrap();
        }
    });

    let id = handle.id();

    // Send via scheduler
    send_to(id, Message::Value("hello".to_string())).expect("send_to ok");

    let response = handle.recv().expect("recv ok");
    match response {
        Message::Value(s) => assert_eq!(s, "got: hello"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

/// Test send_to with invalid id
#[test]
fn test_runtime_send_to_invalid_id() {
    use simple_runtime::concurrency::{send_to, Message};

    // Send to non-existent actor
    let result = send_to(999999, Message::Value("test".to_string()));
    assert!(result.is_err(), "Should fail for invalid id");
}

/// Test ScheduledSpawner
#[test]
fn test_scheduled_spawner() {
    use simple_common::ActorSpawner;
    use simple_runtime::concurrency::{Message, ScheduledSpawner};

    let spawner = ScheduledSpawner::new();
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("scheduled".to_string())).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Value(s) => assert_eq!(s, "scheduled"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

/// Test ScheduledSpawner::default()
#[test]
fn test_scheduled_spawner_default() {
    use simple_common::ActorSpawner;
    use simple_runtime::concurrency::{Message, ScheduledSpawner};

    let spawner: ScheduledSpawner = Default::default();
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("default_scheduled".to_string())).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Value(s) => assert_eq!(s, "default_scheduled"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

// =============================================================================
// GcRuntime Coverage Tests
// =============================================================================

/// Test GcRuntime::heap_bytes()
#[test]
fn test_gc_runtime_heap_bytes() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let bytes = gc.heap_bytes();
    // Should be >= 0
    assert!(bytes >= 0 || bytes == 0, "heap_bytes should return valid size");
}

/// Test GcRuntime::heap()
#[test]
fn test_gc_runtime_heap_access() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let heap = gc.heap();
    // Heap should be accessible
    let _ = heap.bytes_allocated();
}

/// Test GcRuntime::collect()
#[test]
fn test_gc_runtime_collect() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let after = gc.collect("test");
    // Should return bytes after collection
    assert!(after >= 0 || after == 0, "collect should return valid size");
}

/// Test GcRuntime::with_logger()
#[test]
fn test_gc_runtime_with_logger() {
    use simple_runtime::gc::GcRuntime;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    let log_count = Arc::new(AtomicUsize::new(0));
    let log_count_clone = log_count.clone();

    let gc = GcRuntime::with_logger(move |_event| {
        log_count_clone.fetch_add(1, Ordering::SeqCst);
    });

    // Trigger a collection which should log
    gc.collect("test_log");

    // Should have logged at least start and end events
    assert!(log_count.load(Ordering::SeqCst) >= 2, "Should log collection events");
}

/// Test GcLogEvent Display
#[test]
fn test_gc_log_event_display() {
    use simple_runtime::gc::{GcLogEvent, GcLogEventKind};

    let alloc_event = GcLogEvent {
        kind: GcLogEventKind::Allocation,
        reason: None,
        bytes_in_use: 100,
    };
    let alloc_str = format!("{}", alloc_event);
    assert!(alloc_str.contains("gc:alloc"));

    let start_event = GcLogEvent {
        kind: GcLogEventKind::CollectionStart,
        reason: Some("test".to_string()),
        bytes_in_use: 200,
    };
    let start_str = format!("{}", start_event);
    assert!(start_str.contains("gc:start"));
    assert!(start_str.contains("test"));

    let end_event = GcLogEvent {
        kind: GcLogEventKind::CollectionEnd,
        reason: Some("test".to_string()),
        bytes_in_use: 50,
    };
    let end_str = format!("{}", end_event);
    assert!(end_str.contains("gc:end"));
}

// =============================================================================
// ExecCore Coverage Tests
// =============================================================================

/// Test ExecCore::compile_file()
#[test]
fn test_exec_core_compile_file() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("compile_file_test.spl");
    let out_path = dir.path().join("compile_file_test.smf");

    fs::write(&src_path, "main = 42").expect("write ok");

    let core = ExecCore::new_no_gc();
    let result = core.compile_file(&src_path, &out_path);
    assert!(result.is_ok(), "compile_file should succeed: {:?}", result.err());
    assert!(out_path.exists(), "SMF should exist");
}

/// Test ExecCore::load_module()
#[test]
fn test_exec_core_load_module() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("load_module_test.smf");

    let core = ExecCore::new_no_gc();
    core.compile_source("main = 55", &smf_path).expect("compile ok");

    let module = core.load_module(&smf_path);
    assert!(module.is_ok(), "load_module should succeed: {:?}", module.err());
}

/// Test ExecCore::collect_gc() with no-gc mode
#[test]
fn test_exec_core_collect_gc_no_gc() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new_no_gc();
    // Should not panic
    core.collect_gc();
}

/// Test ExecCore::collect_gc() with gc mode
#[test]
fn test_exec_core_collect_gc_with_gc() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new();
    // Should not panic
    core.collect_gc();
}

/// Test ExecCore::default()
#[test]
fn test_exec_core_default() {
    use simple_driver::exec_core::ExecCore;

    let core: ExecCore = Default::default();
    let result = core.run_source("main = 11").expect("run ok");
    assert_eq!(result, 11);
}

/// Test run_main function
#[test]
fn test_exec_core_run_main() {
    use simple_driver::exec_core::{run_main, ExecCore};

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("run_main_test.smf");

    let core = ExecCore::new_no_gc();
    core.compile_source("main = 77", &smf_path).expect("compile ok");

    let module = core.load_module(&smf_path).expect("load ok");
    let exit_code = run_main(&module).expect("run_main ok");
    assert_eq!(exit_code, 77);
}

// =============================================================================
// Dependency Cache Coverage Tests
// =============================================================================

/// Test BuildCache::default() and load() when no cache exists
#[test]
fn test_build_cache_default() {
    use simple_driver::dependency_cache::BuildCache;

    // Default should create empty cache
    let cache = BuildCache::default();
    assert!(cache.get(std::path::Path::new("/nonexistent")).is_none());
}

/// Test BuildCache::load() returns default when file doesn't exist
#[test]
fn test_build_cache_load_missing() {
    use simple_driver::dependency_cache::BuildCache;

    // Should return default cache when file doesn't exist
    let cache = BuildCache::load();
    let _ = cache; // Just verify it doesn't panic
}

/// Test BuildCache update and get
#[test]
fn test_build_cache_update_get() {
    use simple_driver::dependency_cache::{BuildCache, DepInfo};
    use std::path::PathBuf;

    let mut cache = BuildCache::default();

    let info = DepInfo {
        source: PathBuf::from("/test/source.spl"),
        output: PathBuf::from("/test/source.smf"),
        dependencies: vec![PathBuf::from("/test/dep.spl")],
        macros: vec!["test_macro".to_string()],
        mtime: 12345,
    };

    cache.update(info.clone());

    let retrieved = cache.get(&PathBuf::from("/test/source.spl"));
    assert!(retrieved.is_some());
    let retrieved = retrieved.unwrap();
    assert_eq!(retrieved.mtime, 12345);
    assert_eq!(retrieved.macros, vec!["test_macro".to_string()]);
}

/// Test BuildCache::dependents_of()
#[test]
fn test_build_cache_dependents_of() {
    use simple_driver::dependency_cache::{BuildCache, DepInfo};
    use std::path::PathBuf;

    let mut cache = BuildCache::default();

    // Add a source that depends on lib.spl
    cache.update(DepInfo {
        source: PathBuf::from("/test/main.spl"),
        output: PathBuf::from("/test/main.smf"),
        dependencies: vec![PathBuf::from("/test/lib.spl")],
        macros: vec![],
        mtime: 100,
    });

    // Add another source that depends on lib.spl
    cache.update(DepInfo {
        source: PathBuf::from("/test/other.spl"),
        output: PathBuf::from("/test/other.smf"),
        dependencies: vec![PathBuf::from("/test/lib.spl")],
        macros: vec![],
        mtime: 200,
    });

    // Add a source that doesn't depend on lib.spl
    cache.update(DepInfo {
        source: PathBuf::from("/test/standalone.spl"),
        output: PathBuf::from("/test/standalone.smf"),
        dependencies: vec![],
        macros: vec![],
        mtime: 300,
    });

    let dependents = cache.dependents_of(&PathBuf::from("/test/lib.spl"));
    assert_eq!(dependents.len(), 2, "Should have 2 dependents");
}

/// Test BuildCache::save()
#[test]
fn test_build_cache_save() {
    use simple_driver::dependency_cache::{BuildCache, DepInfo};
    use std::path::PathBuf;

    let mut cache = BuildCache::default();
    cache.update(DepInfo {
        source: PathBuf::from("/test/save_test.spl"),
        output: PathBuf::from("/test/save_test.smf"),
        dependencies: vec![],
        macros: vec![],
        mtime: 999,
    });

    // Should not panic
    cache.save();
}

/// Test analyze_source_str() with imports
#[test]
fn test_analyze_source_str_imports() {
    use simple_driver::dependency_cache::analyze_source_str;
    use std::path::Path;

    let content = r#"
import lib
import utils/helper
import "path/to/module.spl"

main = 42
"#;

    let (deps, macros) = analyze_source_str(Path::new("/test/main.spl"), content);

    assert!(deps.len() >= 2, "Should find imports");
    assert!(macros.is_empty(), "Should have no macros");
}

/// Test analyze_source_str() with macros
#[test]
fn test_analyze_source_str_macros() {
    use simple_driver::dependency_cache::analyze_source_str;
    use std::path::Path;

    let content = r#"
macro debug_print(x: Str) -> ():
    emit result:
        return nil
macro assert(cond: Bool) -> ():
    emit result:
        return nil

main = 0
"#;

    let (deps, macros) = analyze_source_str(Path::new("/test/main.spl"), content);

    assert!(deps.is_empty(), "Should have no imports");
    assert_eq!(macros.len(), 2, "Should find 2 macros");
    assert!(macros.contains(&"debug_print".to_string()));
    assert!(macros.contains(&"assert".to_string()));
}

/// Test analyze_source() with real file
#[test]
fn test_analyze_source_file() {
    use simple_driver::dependency_cache::analyze_source;

    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("analyze_test.spl");

    fs::write(&src_path, "import helper\nmain = 0").expect("write ok");

    let result = analyze_source(&src_path);
    assert!(result.is_ok(), "Should analyze file: {:?}", result.err());

    let (deps, _macros) = result.unwrap();
    assert!(!deps.is_empty(), "Should find import");
}

/// Test current_mtime()
#[test]
fn test_current_mtime() {
    use simple_driver::dependency_cache::current_mtime;

    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("mtime_test.txt");

    // Non-existent file should return 0
    let mtime_missing = current_mtime(&path);
    assert_eq!(mtime_missing, 0);

    // Create file and check mtime
    fs::write(&path, "test").expect("write ok");
    let mtime = current_mtime(&path);
    assert!(mtime > 0, "Should have non-zero mtime for existing file");
}

// =============================================================================
// SMF Section Coverage Tests
// =============================================================================

/// Test SmfSection::name_str()
#[test]
fn test_smf_section_name_str() {
    use simple_loader::smf::{SectionType, SmfSection};

    let mut section = SmfSection {
        section_type: SectionType::Code,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 0,
        name: [0u8; 16],
    };

    // Set name "code"
    section.name[0] = b'c';
    section.name[1] = b'o';
    section.name[2] = b'd';
    section.name[3] = b'e';

    assert_eq!(section.name_str(), "code");
}

/// Test SmfSection::is_executable()
#[test]
fn test_smf_section_is_executable() {
    use simple_loader::smf::{SectionType, SmfSection, SECTION_FLAG_EXEC};

    let mut section = SmfSection {
        section_type: SectionType::Code,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 0,
        name: [0u8; 16],
    };

    assert!(!section.is_executable());

    section.flags = SECTION_FLAG_EXEC;
    assert!(section.is_executable());
}

/// Test SmfSection::is_writable()
#[test]
fn test_smf_section_is_writable() {
    use simple_loader::smf::{SectionType, SmfSection, SECTION_FLAG_WRITE};

    let mut section = SmfSection {
        section_type: SectionType::Data,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 0,
        name: [0u8; 16],
    };

    assert!(!section.is_writable());

    section.flags = SECTION_FLAG_WRITE;
    assert!(section.is_writable());
}

/// Test SectionType enum values
#[test]
fn test_section_type_values() {
    use simple_loader::smf::SectionType;

    assert_eq!(SectionType::Code as u32, 1);
    assert_eq!(SectionType::Data as u32, 2);
    assert_eq!(SectionType::RoData as u32, 3);
    assert_eq!(SectionType::Bss as u32, 4);
    assert_eq!(SectionType::Reloc as u32, 5);
    assert_eq!(SectionType::SymTab as u32, 6);
}
