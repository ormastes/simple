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

    /// Parse the sandbox capability grants for one sandbox out of a rendered
    /// security document.
    ///
    /// Accepts both documents the compiler emits: `sandbox_manifest.sdn`, which
    /// lists grants under `capabilities:`, and `sandbox_lowering.sdn`, which
    /// lists the same grants under `capability_handles:`.
    ///
    /// Sandbox names are recognised by indentation rather than by an allow-list
    /// of structural keys: the first indented `name:` header establishes the
    /// sandbox-name column, and every deeper `key:` header is structural. The
    /// previous allow-list (`capabilities` / `deny` / `allow`) silently treated
    /// `enforcement:` and `capability_handles:` as sandbox names, so parsing a
    /// real `sandbox_lowering.sdn` always yielded an empty table.
    pub fn from_sandbox_lowering_sdn(sandbox_name: &str, text: &str) -> WasmResult<Self> {
        let mut table = Self::new();
        let mut in_target_sandbox = sandbox_name.is_empty();
        let mut sandbox_column: Option<usize> = None;

        for raw_line in text.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            if line.ends_with(':') && !line.contains(' ') {
                let indent = raw_line.len() - raw_line.trim_start().len();
                let label = line.trim_end_matches(':').trim();
                // Indent 0 is the document root (`sandbox_manifest:` /
                // `sandbox_lowering:`), never a sandbox name.
                if indent > 0 && !label.is_empty() {
                    let column = *sandbox_column.get_or_insert(indent);
                    if indent == column {
                        in_target_sandbox = label == sandbox_name;
                    }
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

    /// A preopen is allowed when the path the *module* can name — the guest
    /// path — is granted.
    ///
    /// This deliberately ignores the host path. The previous `host || guest`
    /// form was a bypass: a grant of `/reports` also admitted host `/reports`
    /// mapped as guest `/etc`, which hands the module a directory the policy
    /// never granted under a name the policy never mentioned. The host side of
    /// the mapping is the deployer's choice and constrains nothing the module
    /// can reach.
    fn allows_preopen(&self, guest_path: &str) -> bool {
        self.path_allowed(guest_path)
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

    /// Attach the capability table declared by a compiled module's sandbox
    /// policy.
    ///
    /// This is the bridge between the compiler, which renders the policy into
    /// `sandbox_manifest.sdn` / `sandbox_lowering.sdn`, and the runtime, which
    /// enforces it in `validate_capabilities`. Without it the table stays
    /// `None` and every grant check short-circuits to "allow".
    ///
    /// `policy_sdn` is either rendered document; `sandbox_name` selects which
    /// declared sandbox applies. Returns an error when the named sandbox is not
    /// present in the document, so a typo'd or renamed policy fails closed
    /// rather than silently disabling enforcement.
    pub fn with_sandbox_policy(self, sandbox_name: &str, policy_sdn: &str) -> WasmResult<Self> {
        if !sandbox_name.is_empty() && !sandbox_policy_declares(sandbox_name, policy_sdn) {
            return Err(WasmError::WasiError(format!(
                "WASI sandbox policy '{}' is not declared in the module's security manifest",
                sandbox_name
            )));
        }
        let table = WasiCapabilityTable::from_sandbox_lowering_sdn(sandbox_name, policy_sdn)?;
        Ok(self.with_capability_table(table))
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

    /// Validate env, stdin and preopen grants against the optional capability
    /// table.
    ///
    /// A `None` table means the module declared no sandbox policy, so there is
    /// nothing to enforce. Whenever a policy *does* exist the table must be
    /// attached — see `WasiConfig::with_sandbox_policy`.
    ///
    /// Note on stdout/stderr: `WasiCapabilityTable` also carries `allow_stdout`
    /// / `allow_stderr` grants, and they are intentionally not enforced here.
    /// `initialize` wires stdout and stderr to in-process capture buffers, not
    /// to the host's stdio, so connecting them grants the module no reach
    /// outside the sandbox. Stdin is different: it carries host-supplied bytes
    /// *into* the module, so it is enforced.
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

        if !self.stdin.lock().unwrap().is_empty() && !table.allow_stdin {
            return Err(WasmError::WasiError(
                "WASI capability denied stdin: policy does not grant Stdin".to_string(),
            ));
        }

        for (host_path, guest_path) in &self.preopened_dirs {
            if !table.allows_preopen(guest_path) {
                return Err(WasmError::WasiError(format!(
                    "WASI capability denied preopen host '{}' as '{}'",
                    host_path, guest_path
                )));
            }
        }

        Ok(())
    }
}

/// List the sandbox policies declared in a rendered `sandbox_manifest.sdn` or
/// `sandbox_lowering.sdn` document, in declaration order.
///
/// Sandbox names are the headers at the first indented column; deeper headers
/// (`capabilities:`, `capability_handles:`, `enforcement:`, `policy_rules:`,
/// ...) are structural keys, not sandboxes.
pub fn declared_sandbox_names(policy_sdn: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut sandbox_column: Option<usize> = None;

    for raw_line in policy_sdn.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') || !line.ends_with(':') || line.contains(' ') {
            continue;
        }
        let indent = raw_line.len() - raw_line.trim_start().len();
        if indent == 0 {
            continue;
        }
        let label = line.trim_end_matches(':').trim();
        if label.is_empty() {
            continue;
        }
        let column = *sandbox_column.get_or_insert(indent);
        if indent == column && !names.iter().any(|existing| existing == label) {
            names.push(label.to_string());
        }
    }

    names
}

fn sandbox_policy_declares(sandbox_name: &str, policy_sdn: &str) -> bool {
    declared_sandbox_names(policy_sdn)
        .iter()
        .any(|name| name == sandbox_name)
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

    /// The compiler's `sandbox_lowering.sdn` nests grants under
    /// `capability_handles:`, behind an `enforcement:` block. The old
    /// allow-list parser treated both of those as sandbox-name headers, so it
    /// silently produced an empty table for the very document it is named
    /// after.
    #[test]
    fn test_capability_table_parses_real_sandbox_lowering_document() {
        let lowering = r#"sandbox_lowering:
  PluginSandbox:
    source_backend: wasi
    lowered_backend: wasi_capabilities
    enforcement:
      - preopened_dirs
      - wasi_capability_table
    capability_handles:
      - ReadDir["/reports"]
      - Env["SIMPLE_ENV"]
    policy_rules:
      net: deny
  OtherSandbox:
    source_backend: wasi
    lowered_backend: wasi_capabilities
    capability_handles:
      - ReadDir["/secrets"]
"#;

        let table = WasiCapabilityTable::from_sandbox_lowering_sdn("PluginSandbox", lowering).unwrap();

        assert!(
            table.read_dirs.contains("/reports"),
            "grants must survive the enforcement block"
        );
        assert!(table.env_keys.contains("SIMPLE_ENV"));
        // Grants belonging to a different sandbox must not leak in.
        assert!(!table.read_dirs.contains("/secrets"));

        assert_eq!(
            declared_sandbox_names(lowering),
            vec!["PluginSandbox".to_string(), "OtherSandbox".to_string()]
        );
    }

    /// A grant names a directory in the *guest* namespace. Matching the host
    /// side too let an ungranted guest path through whenever the host path
    /// happened to match a grant.
    #[test]
    fn test_capability_table_denies_granted_host_mapped_to_ungranted_guest() {
        let table = WasiCapabilityTable::new().grant_read_dir("/reports");
        let config = WasiConfig::new()
            .with_capability_table(table)
            .with_preopen_dir("/reports", "/etc");

        let err = config.validate_capabilities().unwrap_err().to_string();
        assert!(
            err.contains("denied preopen host '/reports' as '/etc'"),
            "unexpected diagnostic: {err}"
        );
    }

    #[test]
    fn test_capability_table_denies_ungranted_stdin() {
        let table = WasiCapabilityTable::new().grant_read_dir("/reports");
        let config = WasiConfig::new()
            .with_capability_table(table)
            .with_stdin(b"host supplied bytes");

        let err = config.validate_capabilities().unwrap_err().to_string();
        assert!(err.contains("denied stdin"), "unexpected diagnostic: {err}");
    }

    #[test]
    fn test_capability_table_allows_granted_stdin() {
        let table = WasiCapabilityTable::new().grant_stdin();
        let config = WasiConfig::new()
            .with_capability_table(table)
            .with_stdin(b"host supplied bytes");

        assert!(config.validate_capabilities().is_ok());
    }

    /// Enforcement must not be disabled by naming a sandbox the module never
    /// declared — that would be a fail-open the caller cannot see.
    #[test]
    fn test_with_sandbox_policy_rejects_undeclared_sandbox() {
        let manifest = "sandbox_manifest:\n  PluginSandbox:\n    capabilities:\n      - ReadDir[\"/reports\"]\n";

        let err = WasiConfig::new()
            .with_sandbox_policy("TypoSandbox", manifest)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("is not declared in the module's security manifest"),
            "unexpected: {err}"
        );
    }

    /// End-to-end through the production bridge: policy grants `/reports`, the
    /// config preopens `/etc`, so the run is refused.
    #[test]
    fn test_sandbox_policy_bridge_denies_ungranted_preopen() {
        let manifest = "sandbox_manifest:\n  PluginSandbox:\n    capabilities:\n      - ReadDir[\"/reports\"]\n";

        let config = WasiConfig::new()
            .with_sandbox_policy("PluginSandbox", manifest)
            .unwrap()
            .with_preopen_dir("/etc", "/etc");

        let err = config.validate_capabilities().unwrap_err().to_string();
        assert!(
            err.contains("denied preopen host '/etc' as '/etc'"),
            "unexpected: {err}"
        );

        // ...and the honest direction: a granted preopen still runs.
        let ok = WasiConfig::new()
            .with_sandbox_policy("PluginSandbox", manifest)
            .unwrap()
            .with_preopen_dir("/srv/reports", "/reports");
        assert!(ok.validate_capabilities().is_ok());
    }
}
