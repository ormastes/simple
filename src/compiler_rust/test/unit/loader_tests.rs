//! Loader unit tests

// Note: Loader tests require actual SMF files, so most are in integration tests
// These are basic unit tests for loader utilities

#[test]
fn test_loader_module_exists() {
    // Basic test to ensure loader module compiles
    use simple_loader::ModuleLoader;
    let _ = std::any::TypeId::of::<ModuleLoader>();
}
