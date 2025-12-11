//! GPU Kernel Definitions


/// A parameter type for GPU kernels.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelParamType {
    /// Storage buffer (read-write).
    StorageBuffer { element_type: String, readonly: bool },
    /// Uniform buffer (read-only constants).
    UniformBuffer { element_type: String },
    /// Scalar value.
    Scalar { element_type: String },
}

/// A parameter definition for a GPU kernel.
#[derive(Debug, Clone)]
pub struct KernelParam {
    /// Parameter name.
    pub name: String,
    /// Parameter type.
    pub param_type: KernelParamType,
    /// Binding index.
    pub binding: u32,
}

/// A GPU kernel definition.
#[derive(Debug, Clone)]
pub struct Kernel {
    /// Kernel name.
    name: String,
    /// Kernel parameters.
    params: Vec<KernelParam>,
    /// Kernel source (in Simple language).
    source: Option<String>,
    /// Work group size hint.
    work_group_size: Option<[u32; 3]>,
    /// Shared memory declarations.
    shared_memory: Vec<SharedMemoryDecl>,
}

/// Shared memory declaration.
#[derive(Debug, Clone)]
pub struct SharedMemoryDecl {
    /// Variable name.
    pub name: String,
    /// Element type.
    pub element_type: String,
    /// Array size.
    pub size: usize,
}

impl Kernel {
    /// Create a new kernel with the given name.
    pub fn new(name: impl Into<String>) -> Self {
        Kernel {
            name: name.into(),
            params: Vec::new(),
            source: None,
            work_group_size: None,
            shared_memory: Vec::new(),
        }
    }

    /// Get the kernel name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Add a parameter to the kernel.
    pub fn add_param(&mut self, param: KernelParam) {
        self.params.push(param);
    }

    /// Add a storage buffer parameter.
    pub fn add_storage_buffer(
        &mut self,
        name: impl Into<String>,
        element_type: impl Into<String>,
        readonly: bool,
        binding: u32,
    ) {
        self.params.push(KernelParam {
            name: name.into(),
            param_type: KernelParamType::StorageBuffer {
                element_type: element_type.into(),
                readonly,
            },
            binding,
        });
    }

    /// Add a uniform buffer parameter.
    pub fn add_uniform_buffer(
        &mut self,
        name: impl Into<String>,
        element_type: impl Into<String>,
        binding: u32,
    ) {
        self.params.push(KernelParam {
            name: name.into(),
            param_type: KernelParamType::UniformBuffer {
                element_type: element_type.into(),
            },
            binding,
        });
    }

    /// Add a scalar parameter.
    pub fn add_scalar(
        &mut self,
        name: impl Into<String>,
        element_type: impl Into<String>,
        binding: u32,
    ) {
        self.params.push(KernelParam {
            name: name.into(),
            param_type: KernelParamType::Scalar {
                element_type: element_type.into(),
            },
            binding,
        });
    }

    /// Get the parameters.
    pub fn params(&self) -> &[KernelParam] {
        &self.params
    }

    /// Set the kernel source.
    pub fn set_source(&mut self, source: impl Into<String>) {
        self.source = Some(source.into());
    }

    /// Get the kernel source.
    pub fn source(&self) -> Option<&str> {
        self.source.as_deref()
    }

    /// Set the work group size hint.
    pub fn set_work_group_size(&mut self, size: [u32; 3]) {
        self.work_group_size = Some(size);
    }

    /// Get the work group size hint.
    pub fn work_group_size(&self) -> Option<[u32; 3]> {
        self.work_group_size
    }

    /// Add a shared memory declaration.
    pub fn add_shared_memory(
        &mut self,
        name: impl Into<String>,
        element_type: impl Into<String>,
        size: usize,
    ) {
        self.shared_memory.push(SharedMemoryDecl {
            name: name.into(),
            element_type: element_type.into(),
            size,
        });
    }

    /// Get shared memory declarations.
    pub fn shared_memory(&self) -> &[SharedMemoryDecl] {
        &self.shared_memory
    }
}

/// A compiled GPU kernel ready for execution.
#[derive(Debug)]
pub struct CompiledKernel {
    /// The original kernel definition.
    kernel: Kernel,
    /// Compiled SPIR-V bytecode (in a real implementation).
    spirv: Option<Vec<u8>>,
    /// Compilation metadata.
    metadata: KernelMetadata,
}

/// Metadata about a compiled kernel.
#[derive(Debug, Default)]
pub struct KernelMetadata {
    /// Number of registers used.
    pub registers_used: u32,
    /// Shared memory used in bytes.
    pub shared_memory_bytes: usize,
    /// Whether the kernel uses atomics.
    pub uses_atomics: bool,
    /// Whether the kernel uses barriers.
    pub uses_barriers: bool,
}

impl CompiledKernel {
    /// Create a new compiled kernel (stub).
    pub fn new(kernel: Kernel) -> Self {
        let shared_mem = kernel
            .shared_memory()
            .iter()
            .map(|s| s.size * 4) // Assume 4 bytes per element
            .sum();

        CompiledKernel {
            kernel,
            spirv: None,
            metadata: KernelMetadata {
                registers_used: 0,
                shared_memory_bytes: shared_mem,
                uses_atomics: false,
                uses_barriers: false,
            },
        }
    }

    /// Get the kernel definition.
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Get the kernel metadata.
    pub fn metadata(&self) -> &KernelMetadata {
        &self.metadata
    }

    /// Check if the kernel has been compiled.
    pub fn is_compiled(&self) -> bool {
        self.spirv.is_some()
    }
}

/// GPU kernel attribute for parsing.
#[derive(Debug, Clone)]
pub struct GpuAttribute {
    /// Work group size override.
    pub work_group_size: Option<[u32; 3]>,
    /// Whether to use fast math.
    pub fast_math: bool,
    /// Required features.
    pub requires: Vec<String>,
}

impl Default for GpuAttribute {
    fn default() -> Self {
        GpuAttribute {
            work_group_size: None,
            fast_math: false,
            requires: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kernel_creation() {
        let mut kernel = Kernel::new("vector_add");
        kernel.add_storage_buffer("a", "f32", true, 0);
        kernel.add_storage_buffer("b", "f32", true, 1);
        kernel.add_storage_buffer("out", "f32", false, 2);

        assert_eq!(kernel.name(), "vector_add");
        assert_eq!(kernel.params().len(), 3);
    }

    #[test]
    fn test_kernel_source() {
        let mut kernel = Kernel::new("test");
        kernel.set_source("let idx = gpu.global_id()");

        assert!(kernel.source().is_some());
        assert!(kernel.source().unwrap().contains("global_id"));
    }

    #[test]
    fn test_shared_memory() {
        let mut kernel = Kernel::new("reduce");
        kernel.add_shared_memory("local_data", "f32", 256);

        assert_eq!(kernel.shared_memory().len(), 1);
        assert_eq!(kernel.shared_memory()[0].size, 256);
    }

    #[test]
    fn test_compiled_kernel() {
        let mut kernel = Kernel::new("test");
        kernel.add_shared_memory("data", "f32", 128);

        let compiled = CompiledKernel::new(kernel);
        assert_eq!(compiled.metadata().shared_memory_bytes, 128 * 4);
    }

    #[test]
    fn test_work_group_size() {
        let mut kernel = Kernel::new("test");
        kernel.set_work_group_size([256, 1, 1]);

        assert_eq!(kernel.work_group_size(), Some([256, 1, 1]));
    }
}
