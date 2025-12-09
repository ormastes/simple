//! Compiler pipeline and SMF generation.
//!
//! This module contains the main compilation pipeline that transforms
//! source code into SMF (Simple Module Format) binaries.

use std::fs;
use std::path::Path;
use std::sync::Arc;

use simple_loader::smf::{
    hash_name, Arch, SectionType, SmfHeader, SmfSection, SmfSymbol, SymbolBinding, SymbolType,
    SMF_FLAG_EXECUTABLE, SMF_MAGIC, SECTION_FLAG_EXEC, SECTION_FLAG_READ,
};
use simple_common::gc::GcAllocator;
use simple_type::check as type_check;
use tracing::instrument;

use crate::CompileError;
use crate::interpreter::evaluate_module;

/// Minimal compiler pipeline that validates syntax then emits a runnable SMF.
pub struct CompilerPipeline {
    gc: Option<Arc<dyn GcAllocator>>,
}

impl CompilerPipeline {
    pub fn new() -> Result<Self, CompileError> {
        Ok(Self { gc: None })
    }

    pub fn with_gc(gc: Arc<dyn GcAllocator>) -> Result<Self, CompileError> {
        Ok(Self { gc: Some(gc) })
    }

    /// Compile a Simple source file to an SMF at `out`.
    ///
    /// Currently supports `main = <integer>` which returns the integer value.
    #[instrument(skip(self, source_path, out))]
    pub fn compile(&mut self, source_path: &Path, out: &Path) -> Result<(), CompileError> {
        let source =
            fs::read_to_string(source_path).map_err(|e| CompileError::Io(format!("{e}")))?;
        let smf_bytes = self.compile_source_to_memory(&source)?;
        fs::write(out, smf_bytes).map_err(|e| CompileError::Io(format!("{e}")))
    }

    /// Compile source string to SMF bytes in memory (no disk I/O).
    #[instrument(skip(self, source))]
    pub fn compile_source_to_memory(&mut self, source: &str) -> Result<Vec<u8>, CompileError> {
        // Parse to ensure the source is syntactically valid.
        let mut parser = simple_parser::Parser::new(source);
        let module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;

        // Type inference/checking (features #13/#14 scaffolding)
        type_check(&module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // Extract the main function's return value
        let main_value = evaluate_module(&module.items)?;

        Ok(generate_smf_bytes(main_value, self.gc.as_ref()))
    }
}

/// Write an SMF binary that returns the given value from main.
pub(crate) fn write_smf_with_return_value(
    path: &Path,
    return_value: i32,
    gc: Option<&Arc<dyn GcAllocator>>,
) -> std::io::Result<()> {
    let buf = generate_smf_bytes(return_value, gc);
    fs::write(path, buf)
}

/// Generate SMF bytes in memory that returns the given value from main.
pub fn generate_smf_bytes(return_value: i32, gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;
    let code_offset = section_table_offset + section_table_size;

    // Generate x86-64 code to return the value
    // mov eax, imm32 = B8 + 4 bytes (little-endian)
    // ret = C3
    let code_bytes = {
        let mut code = Vec::with_capacity(6);
        code.push(0xB8u8); // mov eax, imm32
        code.extend_from_slice(&return_value.to_le_bytes());
        code.push(0xC3); // ret
        code
    };
    if let Some(gc) = gc {
        let _ = gc.alloc_bytes(&code_bytes);
    }
    let symbol_table_offset = code_offset + code_bytes.len() as u64;

    let mut header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: simple_loader::smf::Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 1,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        reserved: [0; 8],
    };

    let mut sec_name = [0u8; 16];
    sec_name[..4].copy_from_slice(b"code");
    let code_section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name: sec_name,
    };

    let string_table = b"main\0".to_vec();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("main"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    };

    header.symbol_table_offset = symbol_table_offset;

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    buf.extend_from_slice(&code_bytes);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    buf
}

/// Helper to write a struct to a byte buffer.
fn push_struct<T: Copy>(buf: &mut Vec<u8>, value: &T) {
    let bytes =
        unsafe { std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>()) };
    buf.extend_from_slice(bytes);
}
