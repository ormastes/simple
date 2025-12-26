//! WASM module runner and execution engine

use crate::error::{WasmError, WasmResult};
use crate::wasi_env::WasiConfig;
use crate::cache::ModuleCache;
use simple_runtime::RuntimeValue;

use std::path::Path;
use std::sync::Arc;

#[cfg(feature = "wasm")]
use wasmer::{Instance, Module, Store};

/// WASM module runner
pub struct WasmRunner {
    /// WASI configuration
    config: WasiConfig,

    /// Module cache
    cache: Arc<ModuleCache>,

    /// Wasmer store
    #[cfg(feature = "wasm")]
    store: Store,
}

impl WasmRunner {
    /// Create a new WASM runner with default configuration
    #[cfg(feature = "wasm")]
    pub fn new() -> WasmResult<Self> {
        Self::with_config(WasiConfig::new())
    }

    /// Create a new WASM runner with custom configuration
    #[cfg(feature = "wasm")]
    pub fn with_config(config: WasiConfig) -> WasmResult<Self> {
        let store = Store::default();
        let cache = Arc::new(ModuleCache::new());

        Ok(Self {
            config,
            cache,
            store,
        })
    }

    /// Run a WASM module from a file
    #[cfg(feature = "wasm")]
    pub fn run_wasm_file(
        &mut self,
        path: &Path,
        function_name: &str,
        args: &[RuntimeValue],
    ) -> WasmResult<RuntimeValue> {
        // Load module
        let module = self.load_module(path)?;

        // Run function
        self.run_function(&module, function_name, args)
    }

    /// Load a WASM module from file (with caching)
    #[cfg(feature = "wasm")]
    fn load_module(&mut self, path: &Path) -> WasmResult<Module> {
        // Check cache first
        if let Some(cached_bytes) = self.cache.get(path)? {
            // Deserialize from cache
            return unsafe { Module::deserialize(&self.store, cached_bytes.as_slice()) }
                .map_err(|e| WasmError::CompilationFailed(e.to_string()));
        }

        // Load and compile module
        let wasm_bytes = std::fs::read(path)?;
        let module = Module::new(&self.store, wasm_bytes)
            .map_err(|e| WasmError::CompilationFailed(e.to_string()))?;

        // Serialize and cache
        let serialized = module
            .serialize()
            .map_err(|e| WasmError::CacheError(e.to_string()))?;
        self.cache.put(path.to_path_buf(), serialized.to_vec())?;

        Ok(module)
    }

    /// Run a function in a WASM module
    #[cfg(feature = "wasm")]
    fn run_function(
        &mut self,
        module: &Module,
        function_name: &str,
        args: &[RuntimeValue],
    ) -> WasmResult<RuntimeValue> {
        use crate::bridge::{extract_result, to_wasm_values};

        // Create WASI environment with capturing pipes
        let (wasi_env, pipes) = self.config.build_wasi_env(&mut self.store)?;

        // Import WASI functions
        let import_object = wasi_env.import_object(&mut self.store, module)
            .map_err(|e| WasmError::WasiError(e.to_string()))?;

        // Instantiate module
        let instance = Instance::new(&mut self.store, module, &import_object)
            .map_err(|e| WasmError::InstantiationFailed(e.to_string()))?;

        // Get the function
        let func = instance
            .exports
            .get_function(function_name)
            .map_err(|_| WasmError::FunctionNotFound(function_name.to_string()))?;

        // Convert arguments
        let wasm_args = to_wasm_values(args)?;

        // Call function
        let results = func
            .call(&mut self.store, &wasm_args)
            .map_err(|e| WasmError::CallFailed(e.to_string()))?;

        // Capture stdout/stderr from WASI pipes
        let pipes_ref = pipes.lock().unwrap();
        self.config.capture_output(&pipes_ref)?;
        drop(pipes_ref);

        // Extract result
        extract_result(&results)
    }

    /// Get the WASI configuration
    pub fn config(&self) -> &WasiConfig {
        &self.config
    }

    /// Get mutable access to the WASI configuration
    pub fn config_mut(&mut self) -> &mut WasiConfig {
        &mut self.config
    }

    /// Clear the module cache
    pub fn clear_cache(&self) {
        self.cache.clear();
    }
}

#[cfg(not(feature = "wasm"))]
impl WasmRunner {
    pub fn new() -> WasmResult<Self> {
        Err(WasmError::FeatureNotEnabled)
    }

    pub fn with_config(_config: WasiConfig) -> WasmResult<Self> {
        Err(WasmError::FeatureNotEnabled)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "wasm")]
    fn test_runner_creation() {
        let runner = WasmRunner::new();
        assert!(runner.is_ok());
    }

    #[test]
    #[cfg(feature = "wasm")]
    fn test_runner_with_config() {
        let config = WasiConfig::new().with_args(&["test", "arg1"]);
        let runner = WasmRunner::with_config(config);
        assert!(runner.is_ok());
    }
}
