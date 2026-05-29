//! WASI environment configuration and setup

use crate::error::{WasmError, WasmResult};
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

/// Explicit capability grants for a WASI instance.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WasiCapabilityTable {
    /// Environment variable names that may be passed to the module.
    pub env_keys: HashSet<String>,

    /// Allows all environment variables when a manifest grants broad Env.
    pub allow_all_env: bool,

    /// Directory paths that may be preopened for read-oriented capabilities.
    pub read_dirs: HashSet<String>,

    /// Directory paths that may be preopened for write-oriented capabilities.
    pub write_dirs: HashSet<String>,

    /// Whether stdin may be connected.
    pub allow_stdin: bool,

    /// Whether stdout may be connected.
    pub allow_stdout: bool,

    /// Whether stderr may be connected.
    pub allow_stderr: bool,
}

impl WasiCapabilityTable {
    /// Create an empty fail-closed capability table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Grant one environment variable.
    pub fn grant_env(mut self, key: &str) -> Self {
        self.env_keys.insert(key.to_string());
        self
    }

    /// Grant all environment variables.
    pub fn grant_all_env(mut self) -> Self {
        self.allow_all_env = true;
        self
    }

    /// Grant a read directory preopen.
    pub fn grant_read_dir(mut self, path: &str) -> Self {
        self.read_dirs.insert(normalize_capability_path(path));
        self
    }

    /// Grant a write directory preopen.
    pub fn grant_write_dir(mut self, path: &str) -> Self {
        self.write_dirs.insert(normalize_capability_path(path));
        self
    }

    /// Grant stdin connection.
    pub fn grant_stdin(mut self) -> Self {
        self.allow_stdin = true;
        self
    }

    /// Grant stdout connection.
    pub fn grant_stdout(mut self) -> Self {
        self.allow_stdout = true;
        self
    }

    /// Grant stderr connection.
    pub fn grant_stderr(mut self) -> Self {
        self.allow_stderr = true;
        self
    }

    /// Parse the lowered sandbox manifest subset used by WASI backends.
    pub fn from_sandbox_lowering_sdn(sandbox_name: &str, text: &str) -> WasmResult<Self> {
        let mut table = Self::new();
        let mut in_target_sandbox = sandbox_name.is_empty();

        for raw_line in text.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            if line.ends_with(':') {
                let label = line.trim_end_matches(':').trim();
                if !label.is_empty() && !matches!(label, "capabilities" | "deny" | "allow") {
                    in_target_sandbox = label == sandbox_name;
                }
            }

            if !in_target_sandbox {
                continue;
            }

            if line.contains("ReadDir") {
                if let Some(path) = extract_capability_argument(line) {
                    table = table.grant_read_dir(&path);
                }
            } else if line.contains("WriteDir") {
                if let Some(path) = extract_capability_argument(line) {
                    table = table.grant_write_dir(&path);
                }
            } else if line.contains("Env") {
                if let Some(key) = extract_capability_argument(line) {
                    table = table.grant_env(&key);
                } else {
                    table = table.grant_all_env();
                }
            } else if line.contains("Stdin") {
                table = table.grant_stdin();
            } else if line.contains("Stdout") {
                table = table.grant_stdout();
            } else if line.contains("Stderr") {
                table = table.grant_stderr();
            }
        }

        Ok(table)
    }

    fn allows_env(&self, key: &str) -> bool {
        self.allow_all_env || self.env_keys.contains(key)
    }

    fn allows_preopen(&self, host_path: &str, guest_path: &str) -> bool {
        self.path_allowed(host_path) || self.path_allowed(guest_path)
    }

    fn path_allowed(&self, path: &str) -> bool {
        let path = normalize_capability_path(path);
        self.read_dirs
            .iter()
            .chain(self.write_dirs.iter())
            .any(|granted| capability_path_matches(granted, &path))
    }
}

/// Configuration for WASI environment
#[derive(Debug, Clone)]
pub struct WasiConfig {
    /// Command-line arguments
    pub args: Vec<String>,

    /// Environment variables
    pub env: HashMap<String, String>,

    /// Pre-opened directories (path -> virtual path)
    pub preopened_dirs: Vec<(String, String)>,

    /// Optional fail-closed capability table for env and preopen grants.
    pub capability_table: Option<WasiCapabilityTable>,

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
            capability_table: None,
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

    /// Attach an explicit WASI capability table.
    pub fn with_capability_table(mut self, table: WasiCapabilityTable) -> Self {
        self.capability_table = Some(table);
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

    /// Validate env and preopen grants against the optional capability table.
    pub fn validate_capabilities(&self) -> WasmResult<()> {
        let Some(table) = &self.capability_table else {
            return Ok(());
        };

        for key in self.env.keys() {
            if !table.allows_env(key) {
                return Err(WasmError::WasiError(format!(
                    "WASI capability denied environment variable '{}'",
                    key
                )));
            }
        }

        for (host_path, guest_path) in &self.preopened_dirs {
            if !table.allows_preopen(host_path, guest_path) {
                return Err(WasmError::WasiError(format!(
                    "WASI capability denied preopen host '{}' as '{}'",
                    host_path, guest_path
                )));
            }
        }

        Ok(())
    }
}

fn normalize_capability_path(path: &str) -> String {
    let trimmed = path.trim().trim_matches('"').trim_end_matches('/');
    if trimmed.is_empty() {
        "/".to_string()
    } else {
        trimmed.to_string()
    }
}

fn capability_path_matches(granted: &str, requested: &str) -> bool {
    requested == granted
        || requested
            .strip_prefix(granted)
            .is_some_and(|rest| rest.starts_with('/'))
}

fn extract_capability_argument(line: &str) -> Option<String> {
    let open = line.find('"')?;
    let rest = &line[open + 1..];
    let close = rest.find('"')?;
    Some(rest[..close].to_string())
}

#[cfg(feature = "wasm")]
use wasmer_wasi::WasiFunctionEnv;

#[cfg(feature = "wasm")]
use std::sync::Arc as StdArc;

#[cfg(feature = "wasm")]
impl WasiConfig {
    /// Create a Wasmer WASI environment from this configuration
    /// Returns the environment and pipes for capturing output
    pub fn build_wasi_env(
        &self,
        store: &mut wasmer::Store,
    ) -> WasmResult<(WasiFunctionEnv, StdArc<Mutex<CapturingPipes>>)> {
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

        self.validate_capabilities()?;

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
        assert!(config.capability_table.is_none());
    }

    #[test]
    fn test_wasi_config_with_args() {
        let config = WasiConfig::new().with_args(&["prog", "arg1", "arg2"]);
        assert_eq!(config.args, vec!["prog", "arg1", "arg2"]);
    }

    #[test]
    fn test_wasi_config_with_env() {
        let config = WasiConfig::new().with_env("KEY1", "VALUE1").with_env("KEY2", "VALUE2");
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

    #[test]
    fn test_wasi_capability_table_allows_declared_env() {
        let table = WasiCapabilityTable::new().grant_env("SIMPLE_ENV");
        let config = WasiConfig::new()
            .with_capability_table(table)
            .with_env("SIMPLE_ENV", "dev");

        assert!(config.validate_capabilities().is_ok());
    }

    #[test]
    fn test_wasi_capability_table_denies_undeclared_env() {
        let table = WasiCapabilityTable::new().grant_env("SIMPLE_ENV");
        let config = WasiConfig::new()
            .with_capability_table(table)
            .with_env("SECRET", "token");

        let err = config.validate_capabilities().unwrap_err().to_string();
        assert!(err.contains("denied environment variable 'SECRET'"));
    }

    #[test]
    fn test_wasi_capability_table_allows_declared_preopen() {
        let table = WasiCapabilityTable::new().grant_read_dir("/reports");
        let config = WasiConfig::new()
            .with_capability_table(table)
            .with_preopen_dir("/srv/reports", "/reports");

        assert!(config.validate_capabilities().is_ok());
    }

    #[test]
    fn test_wasi_capability_table_denies_undeclared_preopen() {
        let table = WasiCapabilityTable::new().grant_read_dir("/reports");
        let config = WasiConfig::new()
            .with_capability_table(table)
            .with_preopen_dir("/etc", "/host-etc");

        let err = config.validate_capabilities().unwrap_err().to_string();
        assert!(err.contains("denied preopen host '/etc' as '/host-etc'"));
    }

    #[test]
    fn test_wasi_capability_table_parses_lowered_wasi_manifest() {
        let manifest = r#"
sandbox_manifest:
    PluginSandbox:
        capabilities:
            - ReadDir("/reports")
            - WriteDir("/tmp/plugin")
            - Env("SIMPLE_ENV")
            - Stdout
    OtherSandbox:
        capabilities:
            - Env("SECRET")
"#;

        let table = WasiCapabilityTable::from_sandbox_lowering_sdn("PluginSandbox", manifest).unwrap();

        assert!(table.read_dirs.contains("/reports"));
        assert!(table.write_dirs.contains("/tmp/plugin"));
        assert!(table.env_keys.contains("SIMPLE_ENV"));
        assert!(!table.env_keys.contains("SECRET"));
        assert!(table.allow_stdout);
    }
}
