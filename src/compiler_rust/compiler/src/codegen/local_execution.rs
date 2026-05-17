//! LocalExecutionManager - unified local JIT execution.
//!
//! Wraps Cranelift JIT (and optionally LLVM JIT) behind the `ExecutionManager`
//! trait, providing a single entry point for local code execution.

use std::sync::Arc;

use crate::mir::MirModule;

use super::execution_manager::{CodeInfo, ExecutionManager, ExecutionResult};
use super::jit::JitCompiler;

use simple_native_loader::{default_runtime_provider, RuntimeSymbolProvider};

/// Which JIT backend to use for local execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JitBackend {
    /// Automatically select the best available backend.
    /// Prefers Cranelift on 64-bit hosts (faster compile times).
    Auto,
    /// Force Cranelift JIT backend.
    Cranelift,
    /// Force LLVM JIT backend (requires `llvm` feature).
    Llvm,
}

impl JitBackend {
    /// Select the best backend for the current host.
    pub fn auto_select() -> JitBackend {
        #[cfg(target_pointer_width = "64")]
        {
            JitBackend::Cranelift
        }
        #[cfg(not(target_pointer_width = "64"))]
        {
            #[cfg(feature = "llvm")]
            {
                JitBackend::Llvm
            }
            #[cfg(not(feature = "llvm"))]
            {
                JitBackend::Cranelift
            }
        }
    }

    /// Select the best backend for a specific target architecture.
    /// Cranelift supports x86_64, aarch64, riscv64; all others route to LLVM.
    pub fn for_target(target: &simple_common::target::Target) -> JitBackend {
        use simple_common::target::TargetArch;
        match target.arch {
            TargetArch::X86_64 | TargetArch::Aarch64 | TargetArch::Riscv64 => JitBackend::Cranelift,
            _ => {
                #[cfg(feature = "llvm")]
                {
                    JitBackend::Llvm
                }
                #[cfg(not(feature = "llvm"))]
                {
                    JitBackend::Cranelift
                }
            }
        }
    }
}

/// Internal enum holding the active JIT backend implementation.
enum JitBackendImpl {
    Cranelift(JitCompiler),
    #[cfg(feature = "llvm")]
    Llvm(super::llvm_jit::LlvmJitCompiler),
}

/// Local execution manager that compiles and runs code in-process.
///
/// Supports Cranelift and (optionally) LLVM JIT backends via the
/// `ExecutionManager` trait.
pub struct LocalExecutionManager {
    backend: JitBackendImpl,
    backend_kind: JitBackend,
}

impl LocalExecutionManager {
    /// Create a new LocalExecutionManager with the specified backend.
    pub fn new(backend: JitBackend) -> Result<Self, String> {
        Self::with_provider(backend, default_runtime_provider())
    }

    /// Create with a specific runtime symbol provider.
    pub fn with_provider(backend: JitBackend, provider: Arc<dyn RuntimeSymbolProvider>) -> Result<Self, String> {
        Self::with_provider_and_target(backend, provider, None)
    }

    /// Create with a specific runtime symbol provider and target.
    /// When target is Some, 32-bit targets automatically route to LLVM.
    pub fn with_provider_and_target(
        backend: JitBackend,
        provider: Arc<dyn RuntimeSymbolProvider>,
        target: Option<simple_common::target::Target>,
    ) -> Result<Self, String> {
        let resolved = match backend {
            JitBackend::Auto => {
                if let Some(ref t) = target {
                    JitBackend::for_target(t)
                } else {
                    JitBackend::auto_select()
                }
            }
            other => other,
        };

        let backend_impl = match resolved {
            JitBackend::Cranelift | JitBackend::Auto => {
                let jit = JitCompiler::with_provider(provider).map_err(|e| format!("Cranelift JIT init: {}", e))?;
                JitBackendImpl::Cranelift(jit)
            }
            #[cfg(feature = "llvm")]
            JitBackend::Llvm => {
                let t = target.unwrap_or_else(simple_common::target::Target::host);
                let jit = super::llvm_jit::LlvmJitCompiler::new_for_target(t)
                    .map_err(|e| format!("LLVM JIT init: {}", e))?;
                JitBackendImpl::Llvm(jit)
            }
            #[cfg(not(feature = "llvm"))]
            JitBackend::Llvm => {
                return Err("LLVM JIT not available: compile with feature 'llvm'".into());
            }
        };

        Ok(Self {
            backend: backend_impl,
            backend_kind: resolved,
        })
    }

    /// Create for a specific target (auto-selects best backend).
    pub fn for_target(target: simple_common::target::Target) -> Result<Self, String> {
        Self::with_provider_and_target(
            JitBackend::Auto,
            default_runtime_provider(),
            Some(target),
        )
    }

    /// Create with Cranelift backend (convenience).
    pub fn cranelift() -> Result<Self, String> {
        Self::new(JitBackend::Cranelift)
    }

    /// Create with auto-selected backend (convenience).
    pub fn auto() -> Result<Self, String> {
        Self::new(JitBackend::Auto)
    }

    /// Get the resolved backend kind.
    pub fn backend_kind(&self) -> JitBackend {
        self.backend_kind
    }
}

impl ExecutionManager for LocalExecutionManager {
    fn compile_module(&mut self, mir: &MirModule) -> Result<CodeInfo, String> {
        match &mut self.backend {
            JitBackendImpl::Cranelift(jit) => {
                jit.compile_module(mir)
                    .map_err(|e| format!("Cranelift JIT compile: {}", e))?;

                let symbol_names: Vec<String> = mir.functions.iter().map(|f| f.name.clone()).collect();

                let entry_point = if mir.functions.iter().any(|f| f.name == "main") {
                    "main".to_string()
                } else {
                    symbol_names.first().cloned().unwrap_or_default()
                };

                Ok(CodeInfo {
                    name: mir.name.clone().unwrap_or_else(|| "module".into()),
                    entry_point,
                    symbol_names,
                })
            }
            #[cfg(feature = "llvm")]
            JitBackendImpl::Llvm(jit) => {
                jit.compile_module(mir)
                    .map_err(|e| format!("LLVM JIT compile: {}", e))?;

                let symbol_names: Vec<String> = mir.functions.iter().map(|f| f.name.clone()).collect();

                let entry_point = if mir.functions.iter().any(|f| f.name == "main") {
                    "main".to_string()
                } else {
                    symbol_names.first().cloned().unwrap_or_default()
                };

                Ok(CodeInfo {
                    name: mir.name.clone().unwrap_or_else(|| "module".into()),
                    entry_point,
                    symbol_names,
                })
            }
        }
    }

    fn execute(&self, name: &str, args: &[i64]) -> Result<i64, String> {
        match &self.backend {
            JitBackendImpl::Cranelift(jit) => {
                // Dispatch based on argument count
                unsafe {
                    match args.len() {
                        0 => jit.call_i64_void(name).map_err(|e| format!("{}", e)),
                        1 => jit.call_i64_i64(name, args[0]).map_err(|e| format!("{}", e)),
                        2 => jit
                            .call_i64_i64_i64(name, args[0], args[1])
                            .map_err(|e| format!("{}", e)),
                        n => Err(format!(
                            "Cranelift JIT: unsupported argument count {} for '{}'",
                            n, name
                        )),
                    }
                }
            }
            #[cfg(feature = "llvm")]
            JitBackendImpl::Llvm(jit) => jit.execute(name, args).map_err(|e| format!("{}", e)),
        }
    }

    fn execute_captured(&self, name: &str, args: &[i64]) -> Result<ExecutionResult, String> {
        use simple_runtime::value::{
            rt_capture_stderr_start, rt_capture_stderr_stop, rt_capture_stdout_start, rt_capture_stdout_stop,
        };

        // Start capturing output
        rt_capture_stdout_start();
        rt_capture_stderr_start();

        // Execute the function
        let result = self.execute(name, args);

        // Stop capturing
        let stdout = rt_capture_stdout_stop();
        let stderr = rt_capture_stderr_stop();

        match result {
            Ok(exit_code) => Ok(ExecutionResult {
                exit_code,
                stdout,
                stderr,
            }),
            Err(e) => {
                // Still return captured output even on error
                Err(format!("{}\nstdout: {}\nstderr: {}", e, stdout, stderr))
            }
        }
    }

    fn has_function(&self, name: &str) -> bool {
        match &self.backend {
            JitBackendImpl::Cranelift(jit) => jit.get_function_ptr(name).is_some(),
            #[cfg(feature = "llvm")]
            JitBackendImpl::Llvm(jit) => jit.has_function(name),
        }
    }

    fn backend_name(&self) -> &str {
        match &self.backend {
            JitBackendImpl::Cranelift(_) => "cranelift-jit",
            #[cfg(feature = "llvm")]
            JitBackendImpl::Llvm(_) => "llvm-jit",
        }
    }

    fn cleanup(&mut self) {
        // Drop and recreate with fresh state
        match self.backend_kind {
            JitBackend::Cranelift | JitBackend::Auto => {
                if let Ok(jit) = JitCompiler::new() {
                    self.backend = JitBackendImpl::Cranelift(jit);
                }
            }
            #[cfg(feature = "llvm")]
            JitBackend::Llvm => {
                if let Ok(jit) = super::llvm_jit::LlvmJitCompiler::new() {
                    self.backend = JitBackendImpl::Llvm(jit);
                }
            }
            #[cfg(not(feature = "llvm"))]
            JitBackend::Llvm => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_common::target::{Target, TargetArch, TargetOs};

    #[test]
    fn test_backend_selection_64bit_targets() {
        let x86_64 = Target { arch: TargetArch::X86_64, os: TargetOs::Linux, ..Target::host() };
        assert_eq!(JitBackend::for_target(&x86_64), JitBackend::Cranelift);

        let aarch64 = Target { arch: TargetArch::Aarch64, os: TargetOs::Linux, ..Target::host() };
        assert_eq!(JitBackend::for_target(&aarch64), JitBackend::Cranelift);

        let rv64 = Target { arch: TargetArch::Riscv64, os: TargetOs::Linux, ..Target::host() };
        assert_eq!(JitBackend::for_target(&rv64), JitBackend::Cranelift);
    }

    #[test]
    fn test_backend_selection_32bit_targets() {
        let x86_32 = Target { arch: TargetArch::X86, os: TargetOs::Linux, ..Target::host() };
        let rv32 = Target { arch: TargetArch::Riscv32, os: TargetOs::Linux, ..Target::host() };
        let arm32 = Target { arch: TargetArch::Arm, os: TargetOs::Linux, ..Target::host() };

        #[cfg(feature = "llvm")]
        {
            assert_eq!(JitBackend::for_target(&x86_32), JitBackend::Llvm);
            assert_eq!(JitBackend::for_target(&rv32), JitBackend::Llvm);
            assert_eq!(JitBackend::for_target(&arm32), JitBackend::Llvm);
        }
        #[cfg(not(feature = "llvm"))]
        {
            assert_eq!(JitBackend::for_target(&x86_32), JitBackend::Cranelift);
            assert_eq!(JitBackend::for_target(&rv32), JitBackend::Cranelift);
            assert_eq!(JitBackend::for_target(&arm32), JitBackend::Cranelift);
        }
    }

    #[test]
    fn test_auto_select_host() {
        let em = LocalExecutionManager::auto();
        assert!(em.is_ok());
        assert_eq!(em.unwrap().backend_kind(), JitBackend::Cranelift);
    }

    #[test]
    fn test_for_target_host() {
        let em = LocalExecutionManager::for_target(Target::host());
        assert!(em.is_ok());
        assert_eq!(em.unwrap().backend_kind(), JitBackend::Cranelift);
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn test_for_target_32bit_uses_llvm() {
        let x86_32 = Target { arch: TargetArch::X86, os: TargetOs::Linux, ..Target::host() };
        let em = LocalExecutionManager::for_target(x86_32);
        assert!(em.is_ok());
        assert_eq!(em.unwrap().backend_kind(), JitBackend::Llvm);
    }
}
