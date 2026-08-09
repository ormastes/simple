use simple_common::{DynLoader, DynModule};
use std::path::Path;

/// Mock module for testing DynModule trait
#[derive(Debug)]
struct MockModule {
    has_main: bool,
}

impl DynModule for MockModule {
    fn get_fn<F: Copy>(&self, name: &str) -> Option<F> {
        if name == "test_fn" {
            // Return a dummy value - in real use this would be a function pointer
            None
        } else {
            None
        }
    }

    fn entry_fn<F: Copy>(&self) -> Option<F> {
        // Would return actual function pointer in real impl if has_main
        let _ = self.has_main;
        None
    }
}

/// Mock error type
#[derive(Debug)]
struct MockError(String);

impl std::fmt::Display for MockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for MockError {}

/// Mock loader for testing DynLoader trait
struct MockLoader {
    should_fail: bool,
}

impl DynLoader for MockLoader {
    type Module = MockModule;
    type Error = MockError;

    fn load(&self, path: &Path) -> Result<Self::Module, Self::Error> {
        if self.should_fail {
            Err(MockError(format!("Failed to load: {}", path.display())))
        } else {
            Ok(MockModule { has_main: true })
        }
    }
}

#[test]
fn dyn_loader_load_success() {
    let loader = MockLoader { should_fail: false };
    let result = loader.load(Path::new("/test/module.so"));
    assert!(result.is_ok());
}

#[test]
fn dyn_loader_load_failure() {
    let loader = MockLoader { should_fail: true };
    let result = loader.load(Path::new("/test/module.so"));
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.to_string().contains("Failed to load"));
}

#[test]
fn dyn_loader_load_with_resolver_uses_default_impl() {
    let loader = MockLoader { should_fail: false };

    // The default implementation ignores the resolver and calls load()
    let result = loader.load_with_resolver(Path::new("/test/module.so"), |name| {
        if name == "external_fn" {
            Some(0x1234)
        } else {
            None
        }
    });

    assert!(result.is_ok());
}

#[test]
fn dyn_loader_load_with_resolver_propagates_error() {
    let loader = MockLoader { should_fail: true };

    let result = loader.load_with_resolver(Path::new("/test/module.so"), |_| None);

    assert!(result.is_err());
}

#[test]
fn dyn_module_get_fn_returns_none_for_unknown() {
    let module = MockModule { has_main: true };
    let result: Option<fn()> = module.get_fn("unknown_function");
    assert!(result.is_none());
}

#[test]
fn dyn_module_entry_fn_behavior() {
    let module_with_main = MockModule { has_main: true };
    let module_without_main = MockModule { has_main: false };

    // Both return None in our mock, but exercise the code paths
    let _: Option<fn()> = module_with_main.entry_fn();
    let _: Option<fn()> = module_without_main.entry_fn();
}
