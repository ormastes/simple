//! Tests for Dependency Injection (DI) constructor injection
//!
//! Tests verify that @sys.inject functions have their dependencies automatically resolved
//! based on DI configuration from simple.toml.

use simple_compiler::{di, hir, mir};
use simple_parser::Parser;

#[test]
fn test_di_basic_constructor_injection() {
    // Test that DI resolves dependencies for @inject constructors
    let source = r#"
class Database:
    fn new() -> Self:
        return Self {}

    fn query(sql: str) -> str:
        return "result"

class UserService:
    @inject
    fn new(db: Database) -> Self:
        return Self {}

fn main():
    # DI should inject Database automatically
    let service = UserService.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Verify UserService.new is marked as inject
    let user_service_new = hir_module
        .functions
        .iter()
        .find(|f| f.name == "UserService.new")
        .expect("Should have UserService.new");
    assert!(user_service_new.inject, "UserService.new should be marked as @inject");

    // Create DI config
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Database)", impl = "Database.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));

    // This should succeed - DI resolves Database dependency
    let result = lowerer.lower_module(&hir_module);

    match result {
        Ok(mir_module) => {
            // Verify MIR was generated
            assert!(!mir_module.functions.is_empty(), "Should have MIR functions");

            // Find the main function
            let main_func = mir_module
                .functions
                .iter()
                .find(|f| f.name == "main")
                .expect("Should have main function");

            // Verify that UserService.new call was generated with injected Database
            // (checking the MIR instructions would require more detailed inspection)
            assert!(!main_func.blocks.is_empty(), "Main should have blocks");
        }
        Err(e) => {
            panic!("DI injection should succeed, but got error: {:?}", e);
        }
    }
}

#[test]
fn test_di_missing_binding_error() {
    // Test that missing DI binding produces a clear error
    let source = r#"
class Logger:
    fn new() -> Self:
        return Self {}

class Service:
    @inject
    fn new(logger: Logger) -> Self:
        return Self {}

fn main():
    let service = Service.new()  # Should fail - no binding for Logger
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create empty DI config (no bindings)
    let di_config = di::DiConfig {
        mode: di::DiMode::Hybrid,
        profiles: std::collections::HashMap::new(),
    };

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should fail with "no DI binding" error
    assert!(result.is_err(), "Should fail when DI binding is missing");

    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("no DI binding") || err_msg.contains("Logger"),
        "Error should mention missing binding: {}",
        err_msg
    );
}

#[test]
fn test_di_binding_selection() {
    // Test that DI selects the correct binding based on priority and specificity
    let source = r#"
class Repository:
    fn new() -> Self:
        return Self {}

    fn save(data: str):
        return nil

class MemoryRepository:
    fn new() -> Self:
        return Self {}

    fn save(data: str):
        return nil

class DatabaseRepository:
    fn new() -> Self:
        return Self {}

    fn save(data: str):
        return nil

class Service:
    @inject
    fn new(repo: Repository) -> Self:
        return Self {}

fn main():
    let service = Service.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config with multiple bindings for Repository
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Repository)", impl = "MemoryRepository.new", scope = "Singleton", priority = 5 },
    { on = "type(Repository)", impl = "DatabaseRepository.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Verify binding selection logic - higher priority should win
    let ctx = di::create_di_match_context("Repository", "", &[]);
    let selected = di_config
        .select_binding("default", &ctx)
        .expect("Should select binding")
        .expect("Should have a binding");

    assert_eq!(
        selected.impl_type, "DatabaseRepository.new",
        "Should select higher priority binding (10 > 5)"
    );
    assert_eq!(selected.priority, 10);
    assert_eq!(selected.scope, di::DiScope::Singleton);
}

#[test]
fn test_di_scope_handling() {
    // Test that DI respects scope (Singleton vs Transient)
    let source = r#"
class Config:
    fn new() -> Self:
        return Self {}

class Service:
    @inject
    fn new(config: Config) -> Self:
        return Self {}
"#;

    let mut parser = Parser::new(source);
    let _ast = parser.parse().expect("Failed to parse");

    // Create DI config with Singleton scope
    let di_toml_singleton = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml_singleton).expect("Failed to parse TOML");
    let di_config_singleton = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    let ctx = di::create_di_match_context("Config", "", &[]);
    let binding = di_config_singleton
        .select_binding("default", &ctx)
        .expect("Should select")
        .expect("Should have binding");

    assert_eq!(binding.scope, di::DiScope::Singleton);

    // Create DI config with Transient scope
    let di_toml_transient = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Transient", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml_transient).expect("Failed to parse TOML");
    let di_config_transient = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    let binding = di_config_transient
        .select_binding("default", &ctx)
        .expect("Should select")
        .expect("Should have binding");

    assert_eq!(binding.scope, di::DiScope::Transient);
}

#[test]
fn test_di_singleton_caching() {
    // Test that Singleton scope reuses the same instance
    let source = r#"
class Config:
    value: i64

    fn new() -> Self:
        return Self { value: 42 }

class ServiceA:
    config: Config

    @inject
    fn new(config: Config) -> Self:
        return Self { config: config }

class ServiceB:
    config: Config

    @inject
    fn new(config: Config) -> Self:
        return Self { config: config }

fn main():
    # Both services should get the SAME Config instance (singleton)
    let serviceA = ServiceA.new()
    let serviceB = ServiceB.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config with Singleton scope
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    match result {
        Ok(mir_module) => {
            // Verify MIR was generated
            assert!(!mir_module.functions.is_empty(), "Should have MIR functions");

            // Find the main function
            let main_func = mir_module
                .functions
                .iter()
                .find(|f| f.name == "main")
                .expect("Should have main function");

            // Count Config.new calls - should be exactly 1 for singleton
            let config_new_calls = main_func.blocks.iter()
                .flat_map(|block| &block.instructions)
                .filter(|inst| {
                    matches!(inst, mir::MirInst::Call { target, .. }
                        if format!("{:?}", target).contains("Config.new"))
                })
                .count();

            // With singleton caching, Config.new should only be called once
            // even though two services depend on it
            assert_eq!(
                config_new_calls, 1,
                "Singleton should only be instantiated once, found {} calls",
                config_new_calls
            );
        }
        Err(e) => {
            panic!("DI singleton caching should work, but got error: {:?}", e);
        }
    }
}

#[test]
fn test_di_transient_creates_multiple_instances() {
    // Test that Transient scope creates new instances each time
    let source = r#"
class Logger:
    fn new() -> Self:
        return Self {}

class ServiceA:
    @inject
    fn new(logger: Logger) -> Self:
        return Self {}

class ServiceB:
    @inject
    fn new(logger: Logger) -> Self:
        return Self {}

fn main():
    # Both services should get DIFFERENT Logger instances (transient)
    let serviceA = ServiceA.new()
    let serviceB = ServiceB.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config with Transient scope
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Logger)", impl = "Logger.new", scope = "Transient", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    match result {
        Ok(mir_module) => {
            // Verify MIR was generated
            assert!(!mir_module.functions.is_empty(), "Should have MIR functions");

            // Find the main function
            let main_func = mir_module
                .functions
                .iter()
                .find(|f| f.name == "main")
                .expect("Should have main function");

            // Count Logger.new calls - should be 2 for transient (one per service)
            let logger_new_calls = main_func.blocks.iter()
                .flat_map(|block| &block.instructions)
                .filter(|inst| {
                    matches!(inst, mir::MirInst::Call { target, .. }
                        if format!("{:?}", target).contains("Logger.new"))
                })
                .count();

            // With transient scope, Logger.new should be called twice
            assert_eq!(
                logger_new_calls, 2,
                "Transient should create new instances each time, found {} calls",
                logger_new_calls
            );
        }
        Err(e) => {
            panic!("DI transient should work, but got error: {:?}", e);
        }
    }
}

#[test]
fn test_di_circular_dependency_direct() {
    // Test that direct circular dependency (A -> B -> A) is detected
    let source = r#"
class ServiceA:
    @inject
    fn new(serviceB: ServiceB) -> Self:
        return Self {}

class ServiceB:
    @inject
    fn new(serviceA: ServiceA) -> Self:
        return Self {}

fn main():
    # This should fail - circular dependency
    let serviceA = ServiceA.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config with bindings that create circular dependency
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(ServiceA)", impl = "ServiceA.new", scope = "Singleton", priority = 10 },
    { on = "type(ServiceB)", impl = "ServiceB.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should fail with circular dependency error
    assert!(result.is_err(), "Should detect circular dependency");

    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("Circular") || err_msg.contains("circular"),
        "Error should mention circular dependency: {}",
        err_msg
    );
}

#[test]
fn test_di_circular_dependency_indirect() {
    // Test that indirect circular dependency (A -> B -> C -> A) is detected
    let source = r#"
class ServiceA:
    @inject
    fn new(serviceB: ServiceB) -> Self:
        return Self {}

class ServiceB:
    @inject
    fn new(serviceC: ServiceC) -> Self:
        return Self {}

class ServiceC:
    @inject
    fn new(serviceA: ServiceA) -> Self:
        return Self {}

fn main():
    # This should fail - indirect circular dependency
    let serviceA = ServiceA.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config with bindings that create indirect circular dependency
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(ServiceA)", impl = "ServiceA.new", scope = "Singleton", priority = 10 },
    { on = "type(ServiceB)", impl = "ServiceB.new", scope = "Singleton", priority = 10 },
    { on = "type(ServiceC)", impl = "ServiceC.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should fail with circular dependency error
    assert!(result.is_err(), "Should detect indirect circular dependency");

    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("Circular") || err_msg.contains("circular"),
        "Error should mention circular dependency: {}",
        err_msg
    );
}

#[test]
fn test_di_no_circular_dependency() {
    // Test that valid dependency chain (A -> B -> C) is allowed
    let source = r#"
class Config:
    fn new() -> Self:
        return Self {}

class Repository:
    @inject
    fn new(config: Config) -> Self:
        return Self {}

class Service:
    @inject
    fn new(repo: Repository) -> Self:
        return Self {}

fn main():
    # This should work - no circular dependency
    let service = Service.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config with linear dependency chain
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Singleton", priority = 10 },
    { on = "type(Repository)", impl = "Repository.new", scope = "Singleton", priority = 10 },
    { on = "type(Service)", impl = "Service.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should succeed - no circular dependency
    match result {
        Ok(mir_module) => {
            assert!(!mir_module.functions.is_empty(), "Should have MIR functions");
        }
        Err(e) => {
            panic!("Valid dependency chain should work, but got error: {:?}", e);
        }
    }
}

#[test]
fn test_di_per_parameter_inject_mixed() {
    // Test per-parameter @inject with mixed injectable and manual parameters
    let source = r#"
class Config:
    fn new() -> Self:
        return Self {}

class Service:
    fn new(@inject config: Config, manual_id: i64) -> Self:
        return Self {}

fn main():
    # config is injected, manual_id must be provided
    let service = Service.new(42)
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should succeed - config is injected, manual_id is provided
    match result {
        Ok(mir_module) => {
            assert!(!mir_module.functions.is_empty(), "Should have MIR functions");
        }
        Err(e) => {
            panic!("Per-parameter injection should work, but got error: {:?}", e);
        }
    }
}

#[test]
fn test_di_per_parameter_inject_all() {
    // Test per-parameter @inject with all parameters injectable
    let source = r#"
class Config:
    fn new() -> Self:
        return Self {}

class Logger:
    fn new() -> Self:
        return Self {}

class Service:
    fn new(@inject config: Config, @inject logger: Logger) -> Self:
        return Self {}

fn main():
    # Both config and logger are injected
    let service = Service.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Singleton", priority = 10 },
    { on = "type(Logger)", impl = "Logger.new", scope = "Transient", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should succeed - both parameters are injected
    match result {
        Ok(mir_module) => {
            assert!(!mir_module.functions.is_empty(), "Should have MIR functions");
        }
        Err(e) => {
            panic!("All-parameter injection should work, but got error: {:?}", e);
        }
    }
}

#[test]
fn test_di_per_parameter_inject_order() {
    // Test per-parameter @inject with parameters in different order
    let source = r#"
class Config:
    fn new() -> Self:
        return Self {}

class Service:
    fn new(manual_id: i64, @inject config: Config, manual_name: str) -> Self:
        return Self {}

fn main():
    # config is injected (middle param), id and name are manual
    let service = Service.new(42, "test")
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should succeed - config injected in middle position
    match result {
        Ok(mir_module) => {
            assert!(!mir_module.functions.is_empty(), "Should have MIR functions");
        }
        Err(e) => {
            panic!("Middle-position injection should work, but got error: {:?}", e);
        }
    }
}

#[test]
fn test_di_per_parameter_inject_missing_manual_arg() {
    // Test that missing manual arguments produce an error
    let source = r#"
class Config:
    fn new() -> Self:
        return Self {}

class Service:
    fn new(@inject config: Config, manual_id: i64) -> Self:
        return Self {}

fn main():
    # Error: manual_id is not provided
    let service = Service.new()
    return 0
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Create DI config
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
    { on = "type(Config)", impl = "Config.new", scope = "Singleton", priority = 10 }
]
"#;

    let toml_value: toml::Value = toml::from_str(di_toml).expect("Failed to parse TOML");
    let di_config = di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config");

    // Lower to MIR with DI config
    let lowerer = mir::MirLowerer::new().with_di_config(Some(di_config));
    let result = lowerer.lower_module(&hir_module);

    // Should fail - manual_id is not provided
    assert!(result.is_err(), "Should fail when manual argument is missing");

    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("missing argument") || err_msg.contains("Missing"),
        "Error should mention missing argument: {}",
        err_msg
    );
}
