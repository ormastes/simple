//! AOT (Ahead-of-Time) compilation using Cranelift with ObjectModule.

use cranelift_object::{ObjectBuilder, ObjectModule};

use simple_common::target::Target;

use crate::mir::MirModule;

use super::common_backend::{create_isa_and_flags, BackendError, BackendResult, BackendSettings, CodegenBackend};

// Re-export error types for backwards compatibility
pub use super::common_backend::BackendError as CodegenError;
pub type CodegenResult<T> = BackendResult<T>;

/// AOT Codegen context for translating MIR to object code
pub struct Codegen {
    backend: CodegenBackend<ObjectModule>,
}

impl Codegen {
    /// Create a new codegen for the host target.
    pub fn new() -> CodegenResult<Self> {
        Self::for_target(Target::host())
    }

    /// Create a new codegen for a specific target.
    ///
    /// This enables cross-compilation to different architectures.
    pub fn for_target(target: Target) -> CodegenResult<Self> {
        let settings = BackendSettings::aot_for_target(target);
        let (_flags, isa) = create_isa_and_flags(&settings)?;

        let builder = ObjectBuilder::new(isa, "simple_module", cranelift_module::default_libcall_names())
            .map_err(|e| BackendError::ModuleError(e.to_string()))?;

        let module = ObjectModule::new(builder);
        let backend = CodegenBackend::with_module_and_target(module, target)?;

        Ok(Self { backend })
    }

    /// Get the target this codegen is compiling for.
    pub fn target(&self) -> &Target {
        self.backend.target()
    }

    /// Set the module prefix for name mangling in multi-file builds.
    pub fn set_module_prefix(&mut self, prefix: String) {
        self.backend.set_module_prefix(prefix);
    }

    /// Mark this module as the program entry point.
    ///
    /// When `true`, the `main` function is emitted as `spl_main` with
    /// Preemptible linkage. Non-entry modules mangle `main` like any
    /// other local function to avoid symbol collisions.
    pub fn set_entry_module(&mut self, is_entry: bool) {
        self.backend.set_entry_module(is_entry);
    }

    /// Set the import map for cross-module function resolution.
    pub fn set_import_map(&mut self, map: std::sync::Arc<std::collections::HashMap<String, String>>) {
        self.backend.set_import_map(map);
    }

    /// Set the ambiguous names for symbol resolution.
    pub fn set_ambiguous_names(&mut self, names: std::sync::Arc<std::collections::HashSet<String>>) {
        self.backend.set_ambiguous_names(names);
    }

    /// Set the per-module use map for resolving imports from `use` statements.
    pub fn set_use_map(&mut self, map: std::collections::HashMap<String, String>) {
        self.backend.set_use_map(map);
    }

    /// Get a reference to the inner backend for accessing mangling and resolution state.
    pub fn backend(&self) -> &CodegenBackend<ObjectModule> {
        &self.backend
    }

    /// Compile a MIR module to object code.
    pub fn compile_module(mut self, mir: &MirModule) -> CodegenResult<Vec<u8>> {
        // Compile all functions
        self.backend.compile_all_functions(mir)?;

        // Emit object code
        let product = self.backend.module.finish();
        let bytes = product.emit().map_err(|e| BackendError::ModuleError(e.to_string()))?;
        Ok(fix_macho_strsize(bytes))
    }

    /// Finish compilation and get the raw object code.
    pub fn get_object_code(self) -> Vec<u8> {
        let product = self.backend.module.finish();
        let bytes = product.emit().unwrap();
        fix_macho_strsize(bytes)
    }
}

/// Fix Cranelift Mach-O object emission bug: strsize in LC_SYMTAB is 8 bytes too large.
/// The cranelift-object emitter miscalculates the string table size, causing libtool
/// to reject the object file. This pads the file to match the claimed strsize.
fn fix_macho_strsize(mut bytes: Vec<u8>) -> Vec<u8> {
    // Only fix Mach-O 64-bit (magic 0xFEEDFACF)
    if bytes.len() < 32 { return bytes; }
    let magic = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    if magic != 0xFEEDFACF { return bytes; }

    let ncmds = u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]) as usize;
    let mut offset = 32usize;
    for _ in 0..ncmds {
        if offset + 8 > bytes.len() { break; }
        let cmd = u32::from_le_bytes([bytes[offset], bytes[offset+1], bytes[offset+2], bytes[offset+3]]);
        let cmdsize = u32::from_le_bytes([bytes[offset+4], bytes[offset+5], bytes[offset+6], bytes[offset+7]]) as usize;
        if cmd == 2 { // LC_SYMTAB
            if offset + 24 > bytes.len() { break; }
            let stroff = u32::from_le_bytes([bytes[offset+16], bytes[offset+17], bytes[offset+18], bytes[offset+19]]) as usize;
            let strsize = u32::from_le_bytes([bytes[offset+20], bytes[offset+21], bytes[offset+22], bytes[offset+23]]) as usize;
            let needed = stroff + strsize;
            if needed > bytes.len() {
                // Pad with zero bytes to match claimed strsize
                bytes.resize(needed, 0);
            }
            break;
        }
        offset += cmdsize;
    }
    bytes
}

impl Default for Codegen {
    fn default() -> Self {
        Self::new().expect("Failed to create codegen")
    }
}

#[cfg(test)]
#[path = "cranelift_tests.rs"]
mod tests;
