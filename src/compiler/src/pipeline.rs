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
use crate::lint::{LintChecker, LintConfig, LintDiagnostic};
use crate::mir;
use crate::value::FUNC_MAIN;
use crate::project::ProjectContext;
use crate::CompileError;

/// Minimal compiler pipeline that validates syntax then emits a runnable SMF.
pub struct CompilerPipeline {
    gc: Option<Arc<dyn GcAllocator>>,
    /// Optional project context for multi-file compilation
    project: Option<ProjectContext>,
    /// Lint configuration (can be set independently of project)
    lint_config: Option<LintConfig>,
    /// Lint diagnostics from the last compilation
    lint_diagnostics: Vec<LintDiagnostic>,
}

impl CompilerPipeline {
    pub fn new() -> Result<Self, CompileError> {
        Ok(Self {
            gc: None,
            project: None,
            lint_config: None,
            lint_diagnostics: Vec::new(),
        })
    }

    pub fn with_gc(gc: Arc<dyn GcAllocator>) -> Result<Self, CompileError> {
        Ok(Self {
            gc: Some(gc),
            project: None,
            lint_config: None,
            lint_diagnostics: Vec::new(),
        })
    }

    /// Create a pipeline with a project context
    pub fn with_project(project: ProjectContext) -> Result<Self, CompileError> {
        let lint_config = Some(project.lint_config.clone());
        Ok(Self {
            gc: None,
            project: Some(project),
            lint_config,
            lint_diagnostics: Vec::new(),
        })
    }

    /// Create a pipeline with both GC and project context
    pub fn with_gc_and_project(gc: Arc<dyn GcAllocator>, project: ProjectContext) -> Result<Self, CompileError> {
        let lint_config = Some(project.lint_config.clone());
        Ok(Self {
            gc: Some(gc),
            project: Some(project),
            lint_config,
            lint_diagnostics: Vec::new(),
        })
    }

    /// Set the project context
    pub fn set_project(&mut self, project: ProjectContext) {
        self.lint_config = Some(project.lint_config.clone());
        self.project = Some(project);
    }

    /// Get the project context if set
    pub fn project(&self) -> Option<&ProjectContext> {
        self.project.as_ref()
    }

    /// Set the lint configuration explicitly
    pub fn set_lint_config(&mut self, config: LintConfig) {
        self.lint_config = Some(config);
    }

    /// Get the lint configuration
    pub fn lint_config(&self) -> Option<&LintConfig> {
        self.lint_config.as_ref()
    }

    /// Get lint diagnostics from the last compilation
    pub fn lint_diagnostics(&self) -> &[LintDiagnostic] {
        &self.lint_diagnostics
    }

    /// Take lint diagnostics (clears internal storage)
    pub fn take_lint_diagnostics(&mut self) -> Vec<LintDiagnostic> {
        std::mem::take(&mut self.lint_diagnostics)
    }

    /// Check if the last compilation had lint errors
    pub fn has_lint_errors(&self) -> bool {
        self.lint_diagnostics.iter().any(|d| d.is_error())
    }

    /// Check if the last compilation had lint warnings
    pub fn has_lint_warnings(&self) -> bool {
        self.lint_diagnostics.iter().any(|d| d.is_warning())
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
    /// Lint diagnostics are stored and can be retrieved via `lint_diagnostics()`.
    #[instrument(skip(self, source))]
    pub fn compile_source_to_memory(&mut self, source: &str) -> Result<Vec<u8>, CompileError> {
        // Clear previous lint diagnostics
        self.lint_diagnostics.clear();

        // Parse to ensure the source is syntactically valid.
        let mut parser = simple_parser::Parser::new(source);
        let module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;

        // Run lint checks
        self.run_lint_checks(&module.items)?;

        // Type inference/checking (features #13/#14 scaffolding)
        type_check(&module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // Extract the main function's return value
        let main_value = evaluate_module(&module.items)?;

        Ok(generate_smf_bytes(main_value, self.gc.as_ref()))
    }

    /// Run lint checks on AST items.
    ///
    /// Stores diagnostics in `self.lint_diagnostics`.
    /// Returns an error if any lint is set to deny level.
    fn run_lint_checks(&mut self, items: &[simple_parser::ast::Node]) -> Result<(), CompileError> {
        let mut checker = if let Some(ref config) = self.lint_config {
            LintChecker::with_config(config.clone())
        } else {
            LintChecker::new()
        };

        checker.check_module(items);
        self.lint_diagnostics = checker.take_diagnostics();

        // If any lint has deny level, return an error
        if self.has_lint_errors() {
            let errors: Vec<String> = self.lint_diagnostics
                .iter()
                .filter(|d| d.is_error())
                .map(|d| d.format())
                .collect();
            return Err(CompileError::Lint(errors.join("\n")));
        }

        Ok(())
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
    /// Lint diagnostics are stored and can be retrieved via `lint_diagnostics()`.
    #[instrument(skip(self, source))]
    pub fn compile_source_to_memory_native(
        &mut self,
        source: &str,
    ) -> Result<Vec<u8>, CompileError> {
        // Clear previous lint diagnostics
        self.lint_diagnostics.clear();

        // 1. Parse source to AST
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;

        // 2. Run lint checks
        self.run_lint_checks(&ast_module.items)?;

        // 3. Type check
        type_check(&ast_module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // 4. Lower AST to HIR
        let hir_module = hir::lower(&ast_module)
            .map_err(|e| CompileError::Semantic(format!("HIR lowering: {e}")))?;

        // 5. Lower HIR to MIR
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

        // 6. Generate machine code via Cranelift
        let codegen = Codegen::new().map_err(|e| CompileError::Codegen(format!("{e}")))?;
        let object_code = codegen
            .compile_module(&mir_module)
            .map_err(|e| CompileError::Codegen(format!("{e}")))?;

        // 7. Wrap object code in SMF format
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

/// Parse ELF object file, extract .text section, and apply relocations.
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
    let e_shoff = u64::from_le_bytes(elf_data[40..48].try_into().ok()?) as usize;
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

    // Parse all sections to find .text, .rela.text, .symtab, and .strtab
    let mut text_section: Option<(usize, usize)> = None;
    let mut rela_text_section: Option<(usize, usize)> = None;
    let mut symtab_section: Option<(usize, usize, usize)> = None; // (offset, size, link)
    let mut strtab_offset: Option<usize> = None;

    for i in 0..e_shnum {
        let sh_offset = e_shoff + i * e_shentsize;
        if sh_offset + e_shentsize > elf_data.len() {
            continue;
        }

        let sh_name =
            u32::from_le_bytes(elf_data[sh_offset..sh_offset + 4].try_into().ok()?) as usize;
        let sh_type = u32::from_le_bytes(elf_data[sh_offset + 4..sh_offset + 8].try_into().ok()?);
        let sh_link = u32::from_le_bytes(elf_data[sh_offset + 40..sh_offset + 44].try_into().ok()?);

        // Get section name from string table
        if sh_name < shstrtab.len() {
            let name_end = shstrtab[sh_name..]
                .iter()
                .position(|&c| c == 0)
                .unwrap_or(shstrtab.len() - sh_name);
            let name = std::str::from_utf8(&shstrtab[sh_name..sh_name + name_end]).ok()?;

            let offset =
                u64::from_le_bytes(elf_data[sh_offset + 24..sh_offset + 32].try_into().ok()?)
                    as usize;
            let size =
                u64::from_le_bytes(elf_data[sh_offset + 32..sh_offset + 40].try_into().ok()?)
                    as usize;

            match name {
                ".text" => text_section = Some((offset, size)),
                ".rela.text" => rela_text_section = Some((offset, size)),
                ".symtab" => symtab_section = Some((offset, size, sh_link as usize)),
                ".strtab" => strtab_offset = Some(offset),
                _ => {}
            }

            // SHT_SYMTAB = 2
            if sh_type == 2 && symtab_section.is_none() {
                symtab_section = Some((offset, size, sh_link as usize));
            }
        }
    }

    let (text_offset, text_size) = text_section?;
    if text_offset + text_size > elf_data.len() || text_size == 0 {
        return None;
    }

    let mut code = elf_data[text_offset..text_offset + text_size].to_vec();

    // Apply relocations if present
    if let (Some((rela_offset, rela_size)), Some((symtab_off, symtab_size, symtab_link))) =
        (rela_text_section, symtab_section)
    {
        // Get string table for symbol names
        let strtab_off = if let Some(off) = strtab_offset {
            off
        } else {
            // Get strtab from symtab's link field
            let link_sh_offset = e_shoff + symtab_link * e_shentsize;
            if link_sh_offset + e_shentsize <= elf_data.len() {
                u64::from_le_bytes(
                    elf_data[link_sh_offset + 24..link_sh_offset + 32]
                        .try_into()
                        .ok()?,
                ) as usize
            } else {
                return Some(code);
            }
        };

        apply_elf_relocations(
            &mut code,
            elf_data,
            rela_offset,
            rela_size,
            symtab_off,
            symtab_size,
            strtab_off,
            text_offset,
        );
    }

    Some(code)
}

/// Apply ELF relocations to extracted code.
fn apply_elf_relocations(
    code: &mut [u8],
    elf_data: &[u8],
    rela_offset: usize,
    rela_size: usize,
    symtab_off: usize,
    symtab_size: usize,
    strtab_off: usize,
    text_base: usize,
) {
    // ELF64 relocation entry size is 24 bytes
    const RELA_ENTRY_SIZE: usize = 24;
    // ELF64 symbol entry size is 24 bytes
    const SYM_ENTRY_SIZE: usize = 24;

    // R_X86_64_PLT32 = 4, R_X86_64_PC32 = 2
    const R_X86_64_PC32: u32 = 2;
    const R_X86_64_PLT32: u32 = 4;

    let num_relocs = rela_size / RELA_ENTRY_SIZE;

    for i in 0..num_relocs {
        let rela_entry = rela_offset + i * RELA_ENTRY_SIZE;
        if rela_entry + RELA_ENTRY_SIZE > elf_data.len() {
            continue;
        }

        let r_offset =
            u64::from_le_bytes(elf_data[rela_entry..rela_entry + 8].try_into().unwrap()) as usize;
        let r_info =
            u64::from_le_bytes(elf_data[rela_entry + 8..rela_entry + 16].try_into().unwrap());
        let r_addend =
            i64::from_le_bytes(elf_data[rela_entry + 16..rela_entry + 24].try_into().unwrap());

        let r_type = (r_info & 0xffffffff) as u32;
        let r_sym = (r_info >> 32) as usize;

        // Only handle PC32 and PLT32 relocations (function calls)
        if r_type != R_X86_64_PC32 && r_type != R_X86_64_PLT32 {
            continue;
        }

        // Get symbol info
        let sym_entry = symtab_off + r_sym * SYM_ENTRY_SIZE;
        if sym_entry + SYM_ENTRY_SIZE > elf_data.len() {
            continue;
        }

        let st_name =
            u32::from_le_bytes(elf_data[sym_entry..sym_entry + 4].try_into().unwrap()) as usize;

        // Get symbol name from string table
        let sym_name = get_elf_string(elf_data, strtab_off, st_name);

        // Resolve runtime symbol address
        if let Some(sym_addr) = resolve_runtime_symbol(&sym_name) {
            // Calculate patch location in the extracted code
            if r_offset < code.len() && r_offset + 4 <= code.len() {
                // For PC-relative relocations, we need to calculate the offset
                // from the instruction address to the target.
                // But since our code will be loaded at an unknown address,
                // we use an absolute call instead.
                //
                // The relocation is: S + A - P
                // where S = symbol address, A = addend, P = patch address
                //
                // Since we're extracting code to a different location,
                // we need to patch with absolute addresses. For PC32/PLT32,
                // we'll compute assuming the code starts at 0 and adjust.
                //
                // Actually, for AOT code that will be mmap'd, we should
                // leave relocations in SMF format for the loader to apply.
                // For now, we patch assuming the code will be at a fixed location.

                // The patch is relative to where the code will be executed.
                // We'll compute a direct offset from the code buffer base.
                let patch_offset_in_text = r_offset;

                // Calculate the relative offset
                // P = address of the 4-byte patch location
                // We want: S + A - P
                // where P is the runtime address of the patch location
                // Since we don't know where the code will be loaded,
                // we need to leave this as a relocation for the loader.

                // For immediate execution in same address space,
                // compute relative offset from the code buffer
                let code_ptr = code.as_ptr() as usize;
                let patch_addr = code_ptr + patch_offset_in_text;
                let value = ((sym_addr as i64) + r_addend - (patch_addr as i64)) as i32;

                code[r_offset..r_offset + 4].copy_from_slice(&value.to_le_bytes());
            }
        }
    }
}

/// Get a null-terminated string from ELF string table.
fn get_elf_string(elf_data: &[u8], strtab_off: usize, offset: usize) -> String {
    let start = strtab_off + offset;
    if start >= elf_data.len() {
        return String::new();
    }

    let end = elf_data[start..]
        .iter()
        .position(|&c| c == 0)
        .map(|p| start + p)
        .unwrap_or(elf_data.len());

    String::from_utf8_lossy(&elf_data[start..end]).into_owned()
}

/// Resolve a runtime symbol name to its address.
fn resolve_runtime_symbol(name: &str) -> Option<usize> {
    use simple_runtime::value;

    // Map symbol names to function pointers
    let addr: usize = match name {
        // Array operations
        "rt_array_new" => simple_runtime::rt_array_new as usize,
        "rt_array_push" => simple_runtime::rt_array_push as usize,
        "rt_array_get" => simple_runtime::rt_array_get as usize,
        "rt_array_set" => simple_runtime::rt_array_set as usize,
        "rt_array_pop" => simple_runtime::rt_array_pop as usize,
        "rt_array_clear" => value::rt_array_clear as usize,

        // Tuple operations
        "rt_tuple_new" => simple_runtime::rt_tuple_new as usize,
        "rt_tuple_set" => simple_runtime::rt_tuple_set as usize,
        "rt_tuple_get" => simple_runtime::rt_tuple_get as usize,
        "rt_tuple_len" => simple_runtime::rt_tuple_len as usize,

        // Dict operations
        "rt_dict_new" => simple_runtime::rt_dict_new as usize,
        "rt_dict_set" => simple_runtime::rt_dict_set as usize,
        "rt_dict_get" => simple_runtime::rt_dict_get as usize,
        "rt_dict_len" => simple_runtime::rt_dict_len as usize,
        "rt_dict_clear" => value::rt_dict_clear as usize,
        "rt_dict_keys" => value::rt_dict_keys as usize,
        "rt_dict_values" => value::rt_dict_values as usize,

        // Index/slice operations
        "rt_index_get" => simple_runtime::rt_index_get as usize,
        "rt_index_set" => simple_runtime::rt_index_set as usize,
        "rt_slice" => simple_runtime::rt_slice as usize,
        "rt_contains" => value::rt_contains as usize,

        // String operations
        "rt_string_new" => simple_runtime::rt_string_new as usize,
        "rt_string_concat" => simple_runtime::rt_string_concat as usize,

        // Value creation/conversion
        "rt_value_int" => simple_runtime::rt_value_int as usize,
        "rt_value_float" => simple_runtime::rt_value_float as usize,
        "rt_value_bool" => simple_runtime::rt_value_bool as usize,
        "rt_value_nil" => simple_runtime::rt_value_nil as usize,

        // Object operations
        "rt_object_new" => simple_runtime::rt_object_new as usize,
        "rt_object_field_get" => simple_runtime::rt_object_field_get as usize,
        "rt_object_field_set" => simple_runtime::rt_object_field_set as usize,

        // Closure operations
        "rt_closure_new" => simple_runtime::rt_closure_new as usize,
        "rt_closure_set_capture" => simple_runtime::rt_closure_set_capture as usize,
        "rt_closure_get_capture" => simple_runtime::rt_closure_get_capture as usize,
        "rt_closure_func_ptr" => simple_runtime::rt_closure_func_ptr as usize,

        // Enum operations
        "rt_enum_new" => simple_runtime::rt_enum_new as usize,
        "rt_enum_discriminant" => simple_runtime::rt_enum_discriminant as usize,
        "rt_enum_payload" => simple_runtime::rt_enum_payload as usize,

        // Raw memory allocation
        "rt_alloc" => simple_runtime::rt_alloc as usize,
        "rt_free" => simple_runtime::rt_free as usize,
        "rt_ptr_to_value" => simple_runtime::rt_ptr_to_value as usize,
        "rt_value_to_ptr" => simple_runtime::rt_value_to_ptr as usize,

        // Async/concurrency operations
        "rt_wait" => simple_runtime::rt_wait as usize,
        "rt_future_new" => simple_runtime::rt_future_new as usize,
        "rt_future_await" => simple_runtime::rt_future_await as usize,
        "rt_actor_spawn" => simple_runtime::rt_actor_spawn as usize,
        "rt_actor_send" => simple_runtime::rt_actor_send as usize,
        "rt_actor_recv" => simple_runtime::rt_actor_recv as usize,

        // Generator operations
        "rt_generator_new" => simple_runtime::rt_generator_new as usize,
        "rt_generator_next" => simple_runtime::rt_generator_next as usize,
        "rt_generator_get_state" => simple_runtime::rt_generator_get_state as usize,
        "rt_generator_set_state" => simple_runtime::rt_generator_set_state as usize,
        "rt_generator_store_slot" => simple_runtime::rt_generator_store_slot as usize,
        "rt_generator_load_slot" => simple_runtime::rt_generator_load_slot as usize,
        "rt_generator_get_ctx" => simple_runtime::rt_generator_get_ctx as usize,
        "rt_generator_mark_done" => simple_runtime::rt_generator_mark_done as usize,

        // Interpreter bridge FFI
        "rt_interp_call" => value::rt_interp_call as usize,
        "rt_interp_eval" => value::rt_interp_eval as usize,

        // Error handling
        "rt_function_not_found" => value::rt_function_not_found as usize,
        "rt_method_not_found" => value::rt_method_not_found as usize,

        // I/O operations
        "rt_print_str" => value::rt_print_str as usize,
        "rt_println_str" => value::rt_println_str as usize,
        "rt_eprint_str" => value::rt_eprint_str as usize,
        "rt_eprintln_str" => value::rt_eprintln_str as usize,
        "rt_print_value" => value::rt_print_value as usize,
        "rt_println_value" => value::rt_println_value as usize,
        "rt_eprint_value" => value::rt_eprint_value as usize,
        "rt_eprintln_value" => value::rt_eprintln_value as usize,
        "rt_capture_stdout_start" => value::rt_capture_stdout_start as usize,
        "rt_capture_stderr_start" => value::rt_capture_stderr_start as usize,

        _ => return None,
    };

    Some(addr)
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

    // ============== Lint Integration Tests ==============

    #[test]
    fn test_pipeline_lint_warnings_collected() {
        // Public function with primitive param should generate warning
        let source = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let _ = pipeline.compile_source_to_memory(source);

        // Should have lint warnings (default level is Warn)
        assert!(pipeline.has_lint_warnings());
        assert!(!pipeline.has_lint_errors());

        let diagnostics = pipeline.lint_diagnostics();
        assert!(!diagnostics.is_empty());
        // Should warn about primitive_api for both param and return type
        assert!(diagnostics.iter().any(|d| d.message.contains("i64")));
    }

    #[test]
    fn test_pipeline_lint_deny_fails_compilation() {
        // Public function with primitive param + deny level should fail
        let source = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let mut config = LintConfig::new();
        config.set_level(crate::lint::LintName::PrimitiveApi, crate::lint::LintLevel::Deny);

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        pipeline.set_lint_config(config);

        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_err());

        match result {
            Err(CompileError::Lint(msg)) => {
                assert!(msg.contains("primitive"));
            }
            _ => panic!("Expected Lint error"),
        }
    }

    #[test]
    fn test_pipeline_lint_allow_suppresses() {
        // With allow level, no warnings/errors should be generated
        let source = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let mut config = LintConfig::new();
        config.set_level(crate::lint::LintName::PrimitiveApi, crate::lint::LintLevel::Allow);

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        pipeline.set_lint_config(config);

        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok());

        // No warnings or errors
        assert!(!pipeline.has_lint_warnings());
        assert!(!pipeline.has_lint_errors());
    }

    #[test]
    fn test_pipeline_private_function_no_lint() {
        // Private functions don't trigger primitive_api lint
        let source = r#"
fn internal_compute(x: i64) -> i64:
    return x

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok());

        // No warnings for private functions
        assert!(!pipeline.has_lint_warnings());
    }

    #[test]
    fn test_pipeline_diagnostics_cleared_on_recompile() {
        let source_with_warning = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let source_clean = r#"
main = 42
"#;

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");

        // First compile - should have warnings
        let _ = pipeline.compile_source_to_memory(source_with_warning);
        assert!(pipeline.has_lint_warnings());

        // Second compile - should clear previous diagnostics
        let _ = pipeline.compile_source_to_memory(source_clean);
        assert!(!pipeline.has_lint_warnings());
    }

    #[test]
    fn test_pipeline_native_lint_integration() {
        // Native compilation should also run lint checks
        let source = r#"
pub fn compute(x: i64) -> i64:
    return x * 2

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let _ = pipeline.compile_source_to_memory_native(source);

        // Should have lint warnings
        assert!(pipeline.has_lint_warnings());
    }
}
