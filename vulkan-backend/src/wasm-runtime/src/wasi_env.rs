//! WASI environment configuration and setup

use crate::error::{WasmError, WasmResult};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// Configuration for WASI environment
#[derive(Debug, Clone)]
pub struct WasiConfig {
    /// Command-line arguments
    pub args: Vec<String>,

    /// Environment variables
    pub env: HashMap<String, String>,

    /// Pre-opened directories (path -> virtual path)
    pub preopened_dirs: Vec<(String, String)>,

    /// Captured stdout
    pub stdout: Arc<Mutex<Vec<u8>>>,

    /// Captured stderr
    pub stderr: Arc<Mutex<Vec<u8>>>,

    /// stdin input
    pub stdin: Arc<Mutex<Vec<u8>>>,
}

impl Default for WasiConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl WasiConfig {
    /// Create a new WASI configuration with defaults
    pub fn new() -> Self {
        Self {
            args: vec!["wasm_module".to_string()],
            env: HashMap::new(),
            preopened_dirs: Vec::new(),
            stdout: Arc::new(Mutex::new(Vec::new())),
            stderr: Arc::new(Mutex::new(Vec::new())),
            stdin: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Set command-line arguments
    pub fn with_args(mut self, args: &[&str]) -> Self {
        self.args = args.iter().map(|s| s.to_string()).collect();
        self
    }

    /// Add a single argument
    pub fn add_arg(mut self, arg: &str) -> Self {
        self.args.push(arg.to_string());
        self
    }

    /// Set an environment variable
    pub fn with_env(mut self, key: &str, value: &str) -> Self {
        self.env.insert(key.to_string(), value.to_string());
        self
    }

    /// Add multiple environment variables
    pub fn with_envs(mut self, envs: &[(&str, &str)]) -> Self {
        for (k, v) in envs {
            self.env.insert(k.to_string(), v.to_string());
        }
        self
    }

    /// Add a pre-opened directory
    pub fn with_preopen_dir(mut self, host_path: &str, guest_path: &str) -> Self {
        self.preopened_dirs
            .push((host_path.to_string(), guest_path.to_string()));
        self
    }

    /// Set stdin data
    pub fn with_stdin(self, data: &[u8]) -> Self {
        *self.stdin.lock().unwrap() = data.to_vec();
        self
    }

    /// Get captured stdout
    pub fn get_stdout(&self) -> Vec<u8> {
        self.stdout.lock().unwrap().clone()
    }

    /// Get captured stdout as string
    pub fn get_stdout_string(&self) -> WasmResult<String> {
        String::from_utf8(self.get_stdout())
            .map_err(|e| WasmError::WasiError(format!("Invalid UTF-8 in stdout: {}", e)))
    }

    /// Get captured stderr
    pub fn get_stderr(&self) -> Vec<u8> {
        self.stderr.lock().unwrap().clone()
    }

    /// Get captured stderr as string
    pub fn get_stderr_string(&self) -> WasmResult<String> {
        String::from_utf8(self.get_stderr())
            .map_err(|e| WasmError::WasiError(format!("Invalid UTF-8 in stderr: {}", e)))
    }

    /// Clear captured stdout
    pub fn clear_stdout(&self) {
        self.stdout.lock().unwrap().clear();
    }

    /// Clear captured stderr
    pub fn clear_stderr(&self) {
        self.stderr.lock().unwrap().clear();
    }
}

#[cfg(feature = "wasm")]
use wasmer_wasi::WasiFunctionEnv;

#[cfg(feature = "wasm")]
use std::sync::Arc as StdArc;

#[cfg(feature = "wasm")]
impl WasiConfig {
    /// Create a Wasmer WASI environment from this configuration
    /// Returns the environment and pipes for capturing output
    pub fn build_wasi_env(&self, store: &mut wasmer::Store) -> WasmResult<(WasiFunctionEnv, StdArc<Mutex<CapturingPipes>>)> {
        use wasmer_wasi::{Pipe, WasiState};

        // Create pipes for stdio
        let mut stdin = Pipe::new();
        let stdout = Pipe::new();
        let stderr = Pipe::new();

        // Write stdin data if provided
        let stdin_data = self.stdin.lock().unwrap().clone();
        if !stdin_data.is_empty() {
            use std::io::Write;
            let _ = stdin.write_all(&stdin_data);
        }

        // Store pipe references for later capture
        let pipes = StdArc::new(Mutex::new(CapturingPipes {
            stdout: StdArc::new(Mutex::new(stdout)),
            stderr: StdArc::new(Mutex::new(stderr)),
        }));

        // Build WASI state
        let mut wasi_state = WasiState::new("simple_wasm");

        // Add arguments
        for arg in &self.args {
            wasi_state.arg(arg);
        }

        // Add environment variables
        for (key, value) in &self.env {
            wasi_state.env(key, value);
        }

        // Add pre-opened directories
        for (host_path, guest_path) in &self.preopened_dirs {
            wasi_state
                .map_dir(guest_path, host_path)
                .map_err(|e| WasmError::WasiError(format!("Failed to map directory: {}", e)))?;
        }

        // Clone pipes for WASI state (they implement Clone)
        let stdout_clone = pipes.lock().unwrap().stdout.lock().unwrap().clone();
        let stderr_clone = pipes.lock().unwrap().stderr.lock().unwrap().clone();

        // Set stdio
        wasi_state.stdin(Box::new(stdin));
        wasi_state.stdout(Box::new(stdout_clone));
        wasi_state.stderr(Box::new(stderr_clone));

        // Finalize WASI environment
        let wasi_env = wasi_state
            .finalize(store)
            .map_err(|e| WasmError::WasiError(format!("Failed to create WASI environment: {}", e)))?;

        Ok((wasi_env, pipes))
    }

    /// Capture output from WASI pipes into internal buffers
    pub fn capture_output(&self, pipes: &CapturingPipes) -> WasmResult<()> {
        use std::io::Read;

        // Read stdout
        let mut stdout_pipe = pipes.stdout.lock().unwrap();
        let mut stdout_data = Vec::new();
        let _ = stdout_pipe.read_to_end(&mut stdout_data);
        *self.stdout.lock().unwrap() = stdout_data;

        // Read stderr
        let mut stderr_pipe = pipes.stderr.lock().unwrap();
        let mut stderr_data = Vec::new();
        let _ = stderr_pipe.read_to_end(&mut stderr_data);
        *self.stderr.lock().unwrap() = stderr_data;

        Ok(())
    }
}

/// Holder for WASI pipes to enable output capture
#[cfg(feature = "wasm")]
pub struct CapturingPipes {
    pub stdout: StdArc<Mutex<wasmer_wasi::Pipe>>,
    pub stderr: StdArc<Mutex<wasmer_wasi::Pipe>>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasi_config_default() {
        let config = WasiConfig::new();
        assert_eq!(config.args, vec!["wasm_module"]);
        assert!(config.env.is_empty());
        assert!(config.preopened_dirs.is_empty());
    }

    #[test]
    fn test_wasi_config_with_args() {
        let config = WasiConfig::new().with_args(&["prog", "arg1", "arg2"]);
        assert_eq!(config.args, vec!["prog", "arg1", "arg2"]);
    }

    #[test]
    fn test_wasi_config_with_env() {
        let config = WasiConfig::new()
            .with_env("KEY1", "VALUE1")
            .with_env("KEY2", "VALUE2");
        assert_eq!(config.env.get("KEY1"), Some(&"VALUE1".to_string()));
        assert_eq!(config.env.get("KEY2"), Some(&"VALUE2".to_string()));
    }

    #[test]
    fn test_wasi_config_stdio() {
        let config = WasiConfig::new().with_stdin(b"test input");
        assert_eq!(*config.stdin.lock().unwrap(), b"test input");
    }

    #[test]
    fn test_wasi_config_capture_stdout() {
        let config = WasiConfig::new();
        *config.stdout.lock().unwrap() = b"test output".to_vec();
        assert_eq!(config.get_stdout_string().unwrap(), "test output");
    }
}
