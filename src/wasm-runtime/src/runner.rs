//! WASM module runner and execution engine

use crate::cache::ModuleCache;
use crate::error::{WasmError, WasmResult};
use crate::wasi_env::WasiConfig;
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
        use wasmer::{ExternType, Global, Imports, Memory, Value as WasmerValue};

        // Check if the module actually needs WASI (has wasi_snapshot_preview1 imports)
        let needs_wasi = module
            .imports()
            .any(|import| import.module() == "wasi_snapshot_preview1");

        // Create WASI environment if needed, or use empty imports
        let (mut wasi_env_opt, pipes, mut import_object) = if needs_wasi {
            let (wasi_env, pipes) = self.config.build_wasi_env(&mut self.store)?;
            let imports = wasi_env
                .import_object(&mut self.store, module)
                .map_err(|e| WasmError::WasiError(e.to_string()))?;
            (Some(wasi_env), Some(pipes), imports)
        } else {
            (None, None, Imports::new())
        };

        // Check what imports the module needs and provide them
        // This handles both linked modules (which define their own memory) and
        // LLVM object files (which expect imports from "env")
        for import in module.imports() {
            let namespace = import.module();
            let name = import.name();

            // Skip imports that WASI already provides
            if namespace == "wasi_snapshot_preview1" {
                continue;
            }

            // Provide env imports for LLVM-generated WASM
            if namespace == "env" {
                match import.ty() {
                    ExternType::Memory(mem_type) => {
                        let memory = Memory::new(&mut self.store, *mem_type).map_err(|e| {
                            WasmError::InstantiationFailed(format!(
                                "Failed to create memory {}: {}",
                                name, e
                            ))
                        })?;
                        import_object.define(namespace, name, memory);
                    }
                    ExternType::Global(glob_type) => {
                        // Provide reasonable defaults for LLVM globals
                        let is_mutable = glob_type.mutability.is_mutable();
                        let value = match (name, is_mutable) {
                            ("__stack_pointer", true) => WasmerValue::I32(65536), // Stack at 64KB
                            ("__heap_base", false) => WasmerValue::I32(32768),    // Heap at 32KB
                            ("__data_end", false) => WasmerValue::I32(1024),      // Data at 1KB
                            ("__table_base", false) => WasmerValue::I32(0),
                            ("__memory_base", false) => WasmerValue::I32(0),
                            _ => WasmerValue::I32(0), // Default for unknown globals
                        };
                        let global = if is_mutable {
                            Global::new_mut(&mut self.store, value)
                        } else {
                            Global::new(&mut self.store, value)
                        };
                        import_object.define(namespace, name, global);
                    }
                    ExternType::Function(_) => {
                        // For unknown functions, we'll let instantiation fail with a clear error
                    }
                    ExternType::Table(_) => {
                        // For tables, we'll let instantiation fail with a clear error
                    }
                }
            }
        }

        // Instantiate module
        let instance = Instance::new(&mut self.store, module, &import_object)
            .map_err(|e| WasmError::InstantiationFailed(e.to_string()))?;

        // Initialize WASI with the instance (required for memory access) if WASI is used
        if let Some(ref mut wasi_env) = wasi_env_opt {
            wasi_env
                .initialize(&mut self.store, &instance)
                .map_err(|e| WasmError::WasiError(format!("Failed to initialize WASI: {}", e)))?;
        }

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

        // Capture stdout/stderr from WASI pipes (only if WASI was used)
        if let Some(ref pipes) = pipes {
            let pipes_ref = pipes.lock().unwrap();
            self.config.capture_output(&pipes_ref)?;
            drop(pipes_ref);
        }

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
