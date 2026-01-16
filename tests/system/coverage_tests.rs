#![allow(unused_imports, unused_variables, deprecated)]
//! Coverage tests: Actor, Interpreter, Runner, ConfigEnv, Loader, Manual Memory
//! Additional coverage tests for various system components

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// Additional Actor Coverage Tests
// =============================================================================

/// Test ActorHandle::id() method
#[test]
fn test_actor_handle_id() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();
    let handle1 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });
    let handle2 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });

    // IDs should be unique
    assert_ne!(handle1.id(), handle2.id(), "Actor IDs should be unique");
    assert!(handle1.id() > 0, "Actor ID should be positive");

    // Clean up
    handle1.recv().unwrap();
    handle2.recv().unwrap();
    handle1.join().unwrap();
    handle2.join().unwrap();
}

/// Test ActorHandle::recv_timeout() method
#[test]
fn test_actor_recv_timeout() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};
    use std::time::Duration;

    let spawner = ThreadSpawner::new();
    let handle = spawner.spawn(|_inbox, outbox| {
        std::thread::sleep(Duration::from_millis(50));
        outbox.send(Message::Value("delayed".to_string())).unwrap();
    });

    // Short timeout should fail
    let result = handle.recv_timeout(Duration::from_millis(10));
    assert!(result.is_err(), "Short timeout should fail");

    // Longer timeout should succeed
    let result = handle.recv_timeout(Duration::from_millis(200));
    assert!(result.is_ok(), "Longer timeout should succeed");
    match result.unwrap() {
        Message::Value(s) => assert_eq!(s, "delayed"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

/// Test ActorHandle::try_recv() method
#[test]
fn test_actor_try_recv() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};
    use std::time::Duration;

    let spawner = ThreadSpawner::new();
    let handle = spawner.spawn(|inbox, outbox| {
        // Wait for signal before sending
        inbox.recv().unwrap();
        outbox.send(Message::Value("ready".to_string())).unwrap();
    });

    // try_recv should return None when no message
    let result = handle.try_recv();
    assert!(result.is_ok());
    assert!(result.unwrap().is_none(), "Should be None when no message");

    // Signal the actor to send
    handle.send(Message::Value("go".to_string())).unwrap();
    std::thread::sleep(Duration::from_millis(50));

    // Now try_recv should get the message
    let result = handle.try_recv();
    assert!(result.is_ok());
    let msg = result.unwrap();
    assert!(msg.is_some(), "Should have message now");
    match msg.unwrap() {
        Message::Value(s) => assert_eq!(s, "ready"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

/// Test ActorHandle::inbox_sender() method
#[test]
fn test_actor_inbox_sender() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();
    let handle = spawner.spawn(|inbox, outbox| {
        if let Ok(msg) = inbox.recv() {
            outbox.send(msg).unwrap();
        }
    });

    // Get the inbox sender and use it directly
    let sender = handle.inbox_sender();
    sender.send(Message::Value("via_sender".to_string())).unwrap();

    let response = handle.recv().unwrap();
    match response {
        Message::Value(s) => assert_eq!(s, "via_sender"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

/// Test ActorHandle equality (PartialEq)
#[test]
fn test_actor_handle_equality() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();
    let handle1 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });

    // Clone should be equal
    let handle1_clone = handle1.clone();
    assert_eq!(handle1, handle1_clone, "Cloned handles should be equal");

    let handle2 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });

    // Different actors should not be equal
    assert_ne!(handle1, handle2, "Different actors should not be equal");

    // Clean up
    handle1.recv().unwrap();
    handle2.recv().unwrap();
    handle1.join().unwrap();
    handle2.join().unwrap();
}

/// Test ThreadSpawner::default()
#[test]
fn test_thread_spawner_default() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner: ThreadSpawner = Default::default();
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("default".to_string())).unwrap();
    });

    let msg = handle.recv().unwrap();
    match msg {
        Message::Value(s) => assert_eq!(s, "default"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

// =============================================================================
// Additional Interpreter Coverage Tests
// =============================================================================

/// Test Interpreter::run_with_stdin()
#[test]
fn test_interpreter_run_with_stdin() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_with_stdin("main = 42", "test input").unwrap();
    assert_eq!(result.exit_code, 42);
}

/// Test Interpreter::gc() method
#[test]
fn test_interpreter_gc_access() {
    let interpreter = Interpreter::new_no_gc();
    // No-GC interpreter should return None for gc()
    assert!(
        interpreter.gc().is_none(),
        "No-GC interpreter should have no GC runtime"
    );
}

/// Test Interpreter::default()
#[test]
fn test_interpreter_default() {
    let interpreter: Interpreter = Default::default();
    let result = interpreter.run_simple("main = 99").unwrap();
    assert_eq!(result.exit_code, 99);
}

/// Test RunResult fields
#[test]
fn test_run_result_fields() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_simple("main = 7").unwrap();

    assert_eq!(result.exit_code, 7);
    assert!(result.stdout.is_empty(), "stdout should be empty for now");
    assert!(result.stderr.is_empty(), "stderr should be empty for now");
}

/// Test RunConfig fields
#[test]
fn test_run_config_fields() {
    let config = RunConfig {
        args: vec!["arg1".to_string(), "arg2".to_string()],
        stdin: "input data".to_string(),
        timeout_ms: 5000,
        in_memory: false,
        running_type: RunningType::default(),
        ..Default::default()
    };

    assert_eq!(config.args.len(), 2);
    assert_eq!(config.stdin, "input data");
    assert_eq!(config.timeout_ms, 5000);
    assert!(!config.in_memory);
}

// =============================================================================
// Additional Runner Coverage Tests
// =============================================================================

/// Test Runner::with_gc_runtime()
#[test]
fn test_runner_with_gc_runtime() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let runner = Runner::with_gc_runtime(gc);
    let result = runner.run_source("main = 33").unwrap();
    assert_eq!(result, 33);
}

/// Test Runner::default()
#[test]
fn test_runner_default() {
    let runner: Runner = Default::default();
    let result = runner.run_source("main = 77").unwrap();
    assert_eq!(result, 77);
}

/// Test Runner::gc() access
#[test]
fn test_runner_gc_access_detailed() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let runner = Runner::with_gc_runtime(gc);

    // Access GC and verify it's accessible
    let gc_ref = runner.gc();
    assert!(std::sync::Arc::strong_count(&gc_ref) >= 1);
}

// =============================================================================
// Additional ConfigEnv Coverage Tests
// =============================================================================

/// Test ConfigEnv::get_or() method
#[test]
fn test_config_env_get_or() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("existing", "value");

    assert_eq!(config.get_or("existing", "default"), "value");
    assert_eq!(config.get_or("missing", "default"), "default");
}

/// Test ConfigEnv short flags (-k value)
#[test]
fn test_config_env_short_flags() {
    use simple_common::ConfigEnv;

    let args = vec!["-p".to_string(), "8080".to_string(), "-v".to_string()];

    let config = ConfigEnv::from_args(&args);
    assert_eq!(config.get("p"), Some("8080"));
    assert_eq!(config.get("v"), Some("true"));
}

/// Test ConfigEnv::contains() method
#[test]
fn test_config_env_contains() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("key", "value");

    assert!(config.contains("key"));
    assert!(!config.contains("nonexistent"));
}

/// Test ConfigEnv clone
#[test]
fn test_config_env_clone() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("key", "value");

    let cloned = config.clone();
    assert_eq!(cloned.get("key"), Some("value"));
}

/// Test ConfigEnv debug
#[test]
fn test_config_env_debug() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("key", "value");

    let debug_str = format!("{:?}", config);
    assert!(debug_str.contains("ConfigEnv"));
}

// =============================================================================
// Additional Loader Coverage Tests
// =============================================================================

/// Test ModuleLoader with resolver
#[test]
fn test_module_loader_with_resolver() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("resolver_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 55", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();

    // Load with a custom resolver
    let result = loader.load_with_resolver(&smf_path, |_symbol| None);
    assert!(result.is_ok(), "Should load with resolver: {:?}", result.err());
}

/// Test loading and executing entry point
#[test]
fn test_module_execute_entry_point() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("execute_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Get and call entry point
    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some());

    let main_fn = entry.unwrap();
    let result = main_fn();
    assert_eq!(result, 42);
}

// =============================================================================
// Additional Manual Memory Coverage Tests
// =============================================================================

/// Test Unique::new() without tracker
#[test]
fn test_unique_new_untracked() {
    use simple_common::Unique;

    let ptr = Unique::new(42);
    assert!(ptr.is_valid());
    assert_eq!(*ptr, 42);

    let value = ptr.into_inner();
    assert_eq!(value, 42);
}

/// Test Unique::is_valid()
#[test]
fn test_unique_is_valid() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let ptr = gc.alloc(100);

    assert!(ptr.is_valid());
    let _ = ptr.into_inner();
    // After into_inner, the original ptr is consumed so we can't check is_valid
}

/// Test Unique debug format
#[test]
fn test_unique_debug() {
    use simple_common::Unique;

    let ptr = Unique::new(42);
    let debug_str = format!("{:?}", ptr);
    assert!(debug_str.contains("Unique"));
    assert!(debug_str.contains("42"));
}

/// Test Shared::new() without tracker
#[test]
fn test_shared_new_untracked() {
    use simple_common::Shared;

    let shared = Shared::new(100);
    assert_eq!(*shared, 100);

    let shared2 = shared.clone();
    assert_eq!(*shared2, 100);
}

/// Test ManualGc::collect()
#[test]
fn test_manual_gc_collect() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    assert_eq!(gc.collect(), 0);

    let _ptr1 = gc.alloc(1);
    let _ptr2 = gc.alloc(2);
    assert_eq!(gc.collect(), 2);
}

// =============================================================================
// ModuleRegistry Coverage Tests
// =============================================================================

/// Test ModuleRegistry::new() and load()
#[test]
fn test_module_registry_new_and_load() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("registry_test.smf");

    // Compile a module first
    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    // Create registry and load
    let registry = ModuleRegistry::new();
    let module = registry.load(&smf_path);
    assert!(module.is_ok(), "Should load module: {:?}", module.err());
}

/// Test ModuleRegistry caching (load same module twice)
#[test]
fn test_module_registry_caching() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("cache_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 100", &smf_path).expect("compile ok");

    let registry = ModuleRegistry::new();

    // First load
    let module1 = registry.load(&smf_path).expect("first load");

    // Second load should return cached
    let module2 = registry.load(&smf_path).expect("second load");

    // Should be the same Arc (cached)
    assert!(
        std::sync::Arc::ptr_eq(&module1, &module2),
        "Should return cached module"
    );
}

/// Test ModuleRegistry::unload()
#[test]
fn test_module_registry_unload() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("unload_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 50", &smf_path).expect("compile ok");

    let registry = ModuleRegistry::new();
    let _ = registry.load(&smf_path).expect("load ok");

    // Unload should succeed
    let unloaded = registry.unload(&smf_path);
    assert!(unloaded, "Should unload successfully");

    // Unload again should return false (already unloaded)
    let unloaded_again = registry.unload(&smf_path);
    assert!(!unloaded_again, "Should return false for already unloaded");
}

/// Test ModuleRegistry::reload()
#[test]
fn test_module_registry_reload() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reload_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 1", &smf_path).expect("compile ok");

    let registry = ModuleRegistry::new();
    let module1 = registry.load(&smf_path).expect("first load");

    // Recompile with different value
    runner.compile_to_smf("main = 2", &smf_path).expect("recompile ok");

    // Reload
    let module2 = registry.reload(&smf_path).expect("reload ok");

    // Should be different Arc (reloaded)
    assert!(!std::sync::Arc::ptr_eq(&module1, &module2), "Should return new module");
}
