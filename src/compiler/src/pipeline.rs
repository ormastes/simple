//! Compiler pipeline and SMF generation.
//!
//! This module contains the main compilation pipeline that transforms
//! source code into SMF (Simple Module Format) binaries.
//!
//! ## Compilation Modes
//!
//! The pipeline supports two compilation modes:
//!
//! 1. **Interpreter mode** (default): Uses the tree-walking interpreter to
//!    evaluate the program, then wraps the result in a minimal SMF binary.
//!    This mode supports all language features.
//!
//! 2. **Native mode**: Compiles through HIR → MIR → Cranelift to generate
//!    actual machine code. This mode is faster but supports fewer features.
//!    Use `compile_native()` or `compile_source_to_memory_native()` for this mode.

use std::fs;
use std::path::Path;
use std::sync::Arc;

use simple_common::gc::GcAllocator;
use simple_loader::smf::{
    hash_name, Arch, SectionType, SmfHeader, SmfSection, SmfSymbol, SymbolBinding, SymbolType,
    SECTION_FLAG_EXEC, SECTION_FLAG_READ, SMF_FLAG_EXECUTABLE, SMF_MAGIC,
};
use simple_type::check as type_check;
use tracing::instrument;

use crate::codegen::Codegen;
use crate::hir;
use crate::interpreter::evaluate_module;
use crate::mir;
use crate::value::FUNC_MAIN;
use crate::project::ProjectContext;
use crate::CompileError;

/// Minimal compiler pipeline that validates syntax then emits a runnable SMF.
pub struct CompilerPipeline {
    gc: Option<Arc<dyn GcAllocator>>,
    /// Optional project context for multi-file compilation
    project: Option<ProjectContext>,
}

impl CompilerPipeline {
    pub fn new() -> Result<Self, CompileError> {
        Ok(Self { gc: None, project: None })
    }

    pub fn with_gc(gc: Arc<dyn GcAllocator>) -> Result<Self, CompileError> {
        Ok(Self { gc: Some(gc), project: None })
    }

    /// Create a pipeline with a project context
    pub fn with_project(project: ProjectContext) -> Result<Self, CompileError> {
        Ok(Self { gc: None, project: Some(project) })
    }

    /// Create a pipeline with both GC and project context
    pub fn with_gc_and_project(gc: Arc<dyn GcAllocator>, project: ProjectContext) -> Result<Self, CompileError> {
        Ok(Self { gc: Some(gc), project: Some(project) })
    }

    /// Set the project context
    pub fn set_project(&mut self, project: ProjectContext) {
        self.project = Some(project);
    }

    /// Get the project context if set
    pub fn project(&self) -> Option<&ProjectContext> {
        self.project.as_ref()
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

    /// Compile a Simple source file with automatic project detection.
    ///
    /// This method searches parent directories for simple.toml and
    /// sets up the project context for module resolution.
    #[instrument(skip(self, source_path, out))]
    pub fn compile_with_project_detection(
        &mut self,
        source_path: &Path,
        out: &Path,
    ) -> Result<(), CompileError> {
        // Detect project context if not already set
        if self.project.is_none() {
            let project = ProjectContext::detect(source_path)?;
            self.project = Some(project);
        }

        self.compile(source_path, out)
    }

    /// Compile source string to SMF bytes in memory (no disk I/O).
    ///
    /// This uses the interpreter mode which supports all language features.
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

    /// Compile a Simple source file to an SMF at `out` using native codegen.
    ///
    /// This uses the native compilation pipeline: HIR → MIR → Cranelift.
    /// Faster execution but supports fewer language features than interpreter mode.
    #[instrument(skip(self, source_path, out))]
    pub fn compile_native(&mut self, source_path: &Path, out: &Path) -> Result<(), CompileError> {
        let source =
            fs::read_to_string(source_path).map_err(|e| CompileError::Io(format!("{e}")))?;
        let smf_bytes = self.compile_source_to_memory_native(&source)?;
        fs::write(out, smf_bytes).map_err(|e| CompileError::Io(format!("{e}")))
    }

    /// Compile source string to SMF bytes using native codegen (HIR → MIR → Cranelift).
    ///
    /// This generates actual machine code rather than using the interpreter.
    /// The resulting SMF can be executed directly.
    #[instrument(skip(self, source))]
    pub fn compile_source_to_memory_native(
        &mut self,
        source: &str,
    ) -> Result<Vec<u8>, CompileError> {
        // 1. Parse source to AST
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;

        // 2. Type check
        type_check(&ast_module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // 3. Lower AST to HIR
        let hir_module = hir::lower(&ast_module)
            .map_err(|e| CompileError::Semantic(format!("HIR lowering: {e}")))?;

        // 4. Lower HIR to MIR
        let mir_module = mir::lower_to_mir(&hir_module)
            .map_err(|e| CompileError::Semantic(format!("MIR lowering: {e}")))?;

        // Check if we have a main function. If not, fall back to interpreter mode.
        // This handles cases like `main = 42` which are module-level constants,
        // not function declarations.
        let has_main_function = mir_module.functions.iter().any(|f| f.name == FUNC_MAIN);

        if !has_main_function {
            // Fallback: evaluate via interpreter and wrap result
            let main_value = evaluate_module(&ast_module.items)?;
            return Ok(generate_smf_bytes(main_value, self.gc.as_ref()));
        }

        // 5. Generate machine code via Cranelift
        let codegen = Codegen::new().map_err(|e| CompileError::Codegen(format!("{e}")))?;
        let object_code = codegen
            .compile_module(&mir_module)
            .map_err(|e| CompileError::Codegen(format!("{e}")))?;

        // 6. Wrap object code in SMF format
        Ok(generate_smf_from_object(&object_code, self.gc.as_ref()))
    }
}

/// Generate SMF from Cranelift object code.
///
/// This wraps the raw object code in an SMF container format that can be
/// loaded and executed by the Simple runtime.
pub fn generate_smf_from_object(object_code: &[u8], gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    // Extract the actual code bytes from the ELF object file format
    let code_bytes = extract_code_from_object(object_code);
    build_smf_with_code(&code_bytes, gc)
}

/// Extract machine code from Cranelift's ELF object output.
///
/// Cranelift produces ELF object files. We need to extract the .text section
/// containing the actual machine code.
fn extract_code_from_object(object_code: &[u8]) -> Vec<u8> {
    // Try to parse as ELF and extract .text section
    if object_code.len() > 4 && &object_code[0..4] == b"\x7fELF" {
        // This is ELF format - try to extract .text
        if let Some(text) = extract_elf_text_section(object_code) {
            return text;
        }
    }

    // Fallback: assume it's raw code or return a stub
    // Return a simple "mov eax, 0; ret" as fallback
    vec![0xB8, 0x00, 0x00, 0x00, 0x00, 0xC3]
}

/// Parse ELF object file and extract .text section.
fn extract_elf_text_section(elf_data: &[u8]) -> Option<Vec<u8>> {
    // Minimal ELF64 parsing to extract .text section
    if elf_data.len() < 64 {
        return None;
    }

    // Check ELF magic
    if &elf_data[0..4] != b"\x7fELF" {
        return None;
    }

    // ELF64 header fields
    let e_shoff = u64::from_le_bytes(elf_data[40..48].try_into().ok()?) as usize; // Section header offset
    let e_shentsize = u16::from_le_bytes(elf_data[58..60].try_into().ok()?) as usize;
    let e_shnum = u16::from_le_bytes(elf_data[60..62].try_into().ok()?) as usize;
    let e_shstrndx = u16::from_le_bytes(elf_data[62..64].try_into().ok()?) as usize;

    if e_shoff == 0 || e_shnum == 0 {
        return None;
    }

    // Find section header string table
    let shstrtab_hdr_offset = e_shoff + e_shstrndx * e_shentsize;
    if shstrtab_hdr_offset + e_shentsize > elf_data.len() {
        return None;
    }
    let shstrtab_offset = u64::from_le_bytes(
        elf_data[shstrtab_hdr_offset + 24..shstrtab_hdr_offset + 32]
            .try_into()
            .ok()?,
    ) as usize;
    let shstrtab_size = u64::from_le_bytes(
        elf_data[shstrtab_hdr_offset + 32..shstrtab_hdr_offset + 40]
            .try_into()
            .ok()?,
    ) as usize;

    if shstrtab_offset + shstrtab_size > elf_data.len() {
        return None;
    }
    let shstrtab = &elf_data[shstrtab_offset..shstrtab_offset + shstrtab_size];

    // Find .text section
    for i in 0..e_shnum {
        let sh_offset = e_shoff + i * e_shentsize;
        if sh_offset + e_shentsize > elf_data.len() {
            continue;
        }

        let sh_name =
            u32::from_le_bytes(elf_data[sh_offset..sh_offset + 4].try_into().ok()?) as usize;

        // Get section name from string table
        if sh_name < shstrtab.len() {
            let name_end = shstrtab[sh_name..]
                .iter()
                .position(|&c| c == 0)
                .unwrap_or(shstrtab.len() - sh_name);
            let name = std::str::from_utf8(&shstrtab[sh_name..sh_name + name_end]).ok()?;

            if name == ".text" {
                let offset =
                    u64::from_le_bytes(elf_data[sh_offset + 24..sh_offset + 32].try_into().ok()?)
                        as usize;
                let size =
                    u64::from_le_bytes(elf_data[sh_offset + 32..sh_offset + 40].try_into().ok()?)
                        as usize;

                if offset + size <= elf_data.len() && size > 0 {
                    return Some(elf_data[offset..offset + size].to_vec());
                }
            }
        }
    }

    None
}

/// Write an SMF binary that returns the given value from main.
#[allow(dead_code)]
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
    build_smf_with_code(&code_bytes, gc)
}

/// Build an SMF module with the given code bytes and a main symbol.
fn build_smf_with_code(code_bytes: &[u8], gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;
    let code_offset = section_table_offset + section_table_size;

    if let Some(gc) = gc {
        let _ = gc.alloc_bytes(code_bytes);
    }
    let symbol_table_offset = code_offset + code_bytes.len() as u64;

    let header = SmfHeader {
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

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    buf.extend_from_slice(code_bytes);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    buf
}

/// Helper to write a struct to a byte buffer.
fn push_struct<T: Copy>(buf: &mut Vec<u8>, value: &T) {
    let bytes = unsafe {
        std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>())
    };
    buf.extend_from_slice(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Debug helper to list ELF sections
    fn list_elf_sections(elf_data: &[u8]) -> Vec<String> {
        let mut sections = Vec::new();

        if elf_data.len() < 64 || &elf_data[0..4] != b"\x7fELF" {
            return sections;
        }

        let e_shoff = u64::from_le_bytes(elf_data[40..48].try_into().unwrap()) as usize;
        let e_shentsize = u16::from_le_bytes(elf_data[58..60].try_into().unwrap()) as usize;
        let e_shnum = u16::from_le_bytes(elf_data[60..62].try_into().unwrap()) as usize;
        let e_shstrndx = u16::from_le_bytes(elf_data[62..64].try_into().unwrap()) as usize;

        if e_shoff == 0 || e_shnum == 0 {
            sections.push(format!("e_shoff={}, e_shnum={}", e_shoff, e_shnum));
            return sections;
        }

        // Get string table
        let shstrtab_hdr_offset = e_shoff + e_shstrndx * e_shentsize;
        if shstrtab_hdr_offset + e_shentsize > elf_data.len() {
            sections.push("shstrtab header out of bounds".to_string());
            return sections;
        }
        let shstrtab_offset = u64::from_le_bytes(
            elf_data[shstrtab_hdr_offset + 24..shstrtab_hdr_offset + 32]
                .try_into()
                .unwrap(),
        ) as usize;
        let shstrtab_size = u64::from_le_bytes(
            elf_data[shstrtab_hdr_offset + 32..shstrtab_hdr_offset + 40]
                .try_into()
                .unwrap(),
        ) as usize;

        if shstrtab_offset + shstrtab_size > elf_data.len() {
            sections.push(format!(
                "shstrtab out of bounds: offset={}, size={}",
                shstrtab_offset, shstrtab_size
            ));
            return sections;
        }
        let shstrtab = &elf_data[shstrtab_offset..shstrtab_offset + shstrtab_size];

        for i in 0..e_shnum {
            let sh_offset = e_shoff + i * e_shentsize;
            if sh_offset + e_shentsize > elf_data.len() {
                continue;
            }

            let sh_name = u32::from_le_bytes(elf_data[sh_offset..sh_offset + 4].try_into().unwrap())
                as usize;

            if sh_name < shstrtab.len() {
                let name_end = shstrtab[sh_name..]
                    .iter()
                    .position(|&c| c == 0)
                    .unwrap_or(shstrtab.len() - sh_name);
                let name =
                    std::str::from_utf8(&shstrtab[sh_name..sh_name + name_end]).unwrap_or("?");

                let sec_offset = u64::from_le_bytes(
                    elf_data[sh_offset + 24..sh_offset + 32].try_into().unwrap(),
                ) as usize;
                let sec_size = u64::from_le_bytes(
                    elf_data[sh_offset + 32..sh_offset + 40].try_into().unwrap(),
                ) as usize;

                sections.push(format!(
                    "Section[{}]: '{}' offset={} size={}",
                    i, name, sec_offset, sec_size
                ));
            }
        }

        sections
    }

    #[test]
    fn test_elf_extraction_from_codegen() {
        // Compile a simple function through Cranelift
        // Note: "main = 42" is a module-level constant, not a function
        // We need an actual function for codegen
        let source = "fn main() -> i64:\n    return 42";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let hir_module = hir::lower(&ast_module).expect("hir lower");

        // Debug: print HIR
        eprintln!("HIR module: {} functions", hir_module.functions.len());
        for func in &hir_module.functions {
            eprintln!("  HIR func: {} (public={})", func.name, func.is_public());
        }

        let mir_module = mir::lower_to_mir(&hir_module).expect("mir lower");

        // Debug: print MIR functions
        eprintln!("MIR functions ({}):", mir_module.functions.len());
        for func in &mir_module.functions {
            eprintln!(
                "  {} (public={}, entry={:?}, blocks={}, params={}, ret={:?})",
                func.name,
                func.is_public(),
                func.entry_block,
                func.blocks.len(),
                func.params.len(),
                func.return_type
            );
            for block in &func.blocks {
                eprintln!("    Block {:?}: {} instructions", block.id, block.instructions.len());
                for inst in &block.instructions {
                    eprintln!("      {:?}", inst);
                }
                eprintln!("      Terminator: {:?}", block.terminator);
            }
        }

        let codegen = crate::codegen::Codegen::new().expect("codegen new");
        let object_code = codegen.compile_module(&mir_module).expect("compile ok");

        // Check if it's ELF
        assert!(
            object_code.len() > 4 && &object_code[0..4] == b"\x7fELF",
            "Expected ELF format, got first 4 bytes: {:?}",
            &object_code[0..4.min(object_code.len())]
        );

        // List all sections for debugging
        let sections = list_elf_sections(&object_code);
        eprintln!("ELF sections:");
        for s in &sections {
            eprintln!("  {}", s);
        }

        // Try to extract .text section
        let text_section = extract_elf_text_section(&object_code);
        assert!(
            text_section.is_some(),
            "Failed to extract .text section from ELF. Sections: {:?}",
            sections
        );

        let text = text_section.unwrap();
        assert!(!text.is_empty(), "Extracted .text section is empty");
        eprintln!("Extracted .text section size: {} bytes", text.len());
        eprintln!("First 16 bytes: {:02x?}", &text[0..16.min(text.len())]);
    }
}
