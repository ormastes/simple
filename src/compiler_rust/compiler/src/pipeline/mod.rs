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
//! 2. **Native mode**: Compiles through HIR → MIR → native backend to generate
//!    actual machine code. This mode is faster but supports fewer features.
//!    Use `compile_native()` or `compile_source_to_memory_native()` for this mode.

pub mod module_loader;
pub mod native_project;
pub mod script_detection;

mod codegen;
mod core;
mod execution;
mod lowering;
mod parsing;

// Re-export main types
pub use core::{CompilerPipeline, SimdMode};
pub use execution::{
    generate_smf_bytes, generate_smf_bytes_for_target, generate_smf_from_object, generate_smf_from_object_for_target,
};

// Re-export startup configuration types (#1979, #1986)
pub use module_loader::{extract_startup_config, StartupAppType, StartupConfig, StartupWindowHints};

// Re-export native project builder types
pub use native_project::{NativeBuildConfig, NativeBuildResult, NativeProjectBuilder};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build_mode::BuildMode;
    use crate::elf_utils::{extract_elf_text_section, get_section_name};
    use crate::hir;
    use crate::import_loader::has_script_statements;
    use crate::lint::{LintConfig, LintLevel, LintName};
    use crate::mir::{self, ContractMode};
    use crate::monomorphize::monomorphize_module;
    use crate::pipeline::SimdMode;
    use crate::CompileError;
    use simple_common::target::{Target, TargetArch, TargetOS};
    use std::path::Path;

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

            let sh_name = u32::from_le_bytes(elf_data[sh_offset..sh_offset + 4].try_into().unwrap()) as usize;

            if let Some(name) = get_section_name(shstrtab, sh_name) {
                let sec_offset =
                    u64::from_le_bytes(elf_data[sh_offset + 24..sh_offset + 32].try_into().unwrap()) as usize;
                let sec_size =
                    u64::from_le_bytes(elf_data[sh_offset + 32..sh_offset + 40].try_into().unwrap()) as usize;

                sections.push(format!(
                    "Section[{}]: '{}' offset={} size={}",
                    i, name, sec_offset, sec_size
                ));
            }
        }

        sections
    }

    fn repo_root() -> std::path::PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("..")
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

        // Check object format based on host platform
        #[cfg(target_os = "macos")]
        {
            // Mach-O 64-bit magic: 0xFEEDFACF (little-endian: CF FA ED FE)
            assert!(
                object_code.len() > 4 && &object_code[0..4] == b"\xcf\xfa\xed\xfe",
                "Expected Mach-O format on macOS, got first 4 bytes: {:?}",
                &object_code[0..4.min(object_code.len())]
            );
            eprintln!("Mach-O object code size: {} bytes", object_code.len());
        }

        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        {
            // ELF magic: 0x7F 'E' 'L' 'F'
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

        #[cfg(target_os = "windows")]
        {
            // COFF magic: first two bytes are machine type (e.g., 0x8664 for x86_64)
            assert!(
                object_code.len() > 2,
                "Expected COFF object, got {} bytes",
                object_code.len()
            );
            eprintln!("COFF object code size: {} bytes", object_code.len());
        }
    }

    #[cfg(not(feature = "llvm"))]
    #[test]
    fn test_pipeline_32bit_target_requires_llvm() {
        let source = "fn main() -> i64:\n    return 42";
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let result = pipeline.compile_source_to_memory_for_target(source, target);

        assert!(result.is_err());
        match result {
            Err(CompileError::Codegen(msg)) => {
                assert!(msg.contains("LLVM backend"));
            }
            other => panic!("Expected codegen error, got {other:?}"),
        }
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn test_pipeline_32bit_target_with_llvm() {
        let source = "fn main() -> i64:\n    return 42";
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let result = pipeline.compile_source_to_memory_for_target(source, target);

        assert!(result.is_ok());
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn test_pipeline_pure_simple_math_core_emits_real_wasm() {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let target = Target::new_wasm(TargetArch::Wasm32, simple_common::target::WasmRuntime::Wasi);
        let entry = repo_root().join("src/app/vscode_extension/math_core/main.spl");

        let bytes = pipeline
            .compile_file_to_memory_for_target(&entry, target)
            .expect("pure-Simple math core should compile to wasm");

        assert!(
            bytes.starts_with(b"\0asm"),
            "expected real wasm magic, got first bytes: {:02x?}",
            &bytes[..bytes.len().min(4)]
        );
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn test_pipeline_wasm_target_rejects_script_fallback() {
        let source = "val x = 1\nfn main() -> i64:\n    return x\n";
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let target = Target::new_wasm(TargetArch::Wasm32, simple_common::target::WasmRuntime::Wasi);
        let result = pipeline.compile_source_to_memory_for_target(source, target);

        match result {
            Err(CompileError::Semantic(message)) => {
                assert!(message.contains("WebAssembly target cannot fall back to SMF/interpreter output"));
            }
            other => panic!("Expected explicit wasm fallback failure, got {other:?}"),
        }
    }

    // ============== Lint Integration Tests ==============

    /// Test helper for running source with a specific lint configuration
    fn run_with_lint_config(source: &str, config: LintConfig) -> Result<Vec<u8>, CompileError> {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        pipeline.set_lint_config(config);
        pipeline.compile_source_to_memory(source)
    }

    #[test]
    fn test_pipeline_lint_warnings_collected() {
        // Mixed types (i64 param + text return) — NOT a pure math function
        let source = r#"
pub fn format_number(x: i64) -> text:
    return "hello"

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let _ = pipeline.compile_source_to_memory(source);

        // Should have lint warnings (default level is Warn)
        assert!(pipeline.has_lint_warnings());
        assert!(!pipeline.has_lint_errors());

        let diagnostics = pipeline.lint_diagnostics();
        assert!(!diagnostics.is_empty());
        // Should warn about primitive_api for the param
        assert!(diagnostics.iter().any(|d| d.message.contains("i64")));
    }

    #[test]
    fn test_pipeline_lint_deny_fails_compilation() {
        // Mixed types (i64 param + text return) + deny level should fail
        let source = r#"
pub fn format_number(x: i64) -> text:
    return "hello"

main = 0
"#;
        let mut config = LintConfig::new();
        config.set_level(LintName::PrimitiveApi, LintLevel::Deny);

        let result = run_with_lint_config(source, config);
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
        config.set_level(LintName::PrimitiveApi, LintLevel::Allow);

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
        // Mixed types — NOT a pure math function
        let source_with_warning = r#"
pub fn format_number(x: i64) -> text:
    return "hello"

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
        // Mixed types (i64 param + text return) — NOT a pure math function
        let source = r#"
pub fn format_number(x: i64) -> text:
    return "hello"

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let _ = pipeline.compile_source_to_memory_native(source);

        // Should have lint warnings
        assert!(pipeline.has_lint_warnings());
    }

    #[test]
    fn script_detection_handles_top_level_match() {
        let mut parser = simple_parser::Parser::new(
            "let x: i32 = 2\nmatch x:\n    2 =>\n        main = 20\n    _ =>\n        main = 0",
        );
        let module = parser.parse().expect("parse ok");
        assert!(
            has_script_statements(&module.items),
            "script statements should be detected for match + let"
        );
    }

    #[test]
    fn interpreter_pipeline_executes_top_level_match() {
        let source = "let x: i32 = 2\nmatch x:\n    2 =>\n        main = 20\n    _ =>\n        main = 0";
        let mut parser = simple_parser::Parser::new(source);
        let ast = parser.parse().expect("parse ok");
        let module = monomorphize_module(&ast);
        let item_kinds: Vec<&str> = module
            .items
            .iter()
            .map(|n| match n {
                simple_parser::ast::Node::Let(_) => "Let",
                simple_parser::ast::Node::Match(_) => "Match",
                simple_parser::ast::Node::Function(_) => "Function",
                _ => "Other",
            })
            .collect();
        assert_eq!(item_kinds, vec!["Let", "Match"]);

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let result = pipeline.compile_source_to_memory(source);
        assert!(
            result.is_ok(),
            "script match should fall back to interpreter, got {result:?}"
        );
    }

    // ============== Contract Mode Integration Tests ==============

    #[test]
    fn test_pipeline_contract_mode_default() {
        let pipeline = CompilerPipeline::new().expect("pipeline ok");
        assert_eq!(pipeline.contract_mode(), ContractMode::All);
    }

    #[test]
    fn test_pipeline_contract_mode_set() {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");

        pipeline.set_contract_mode(ContractMode::Off);
        assert_eq!(pipeline.contract_mode(), ContractMode::Off);

        pipeline.set_contract_mode(ContractMode::Boundary);
        assert_eq!(pipeline.contract_mode(), ContractMode::Boundary);

        pipeline.set_contract_mode(ContractMode::All);
        assert_eq!(pipeline.contract_mode(), ContractMode::All);
    }

    #[test]
    fn test_pipeline_coherence_detects_errors_in_ast() {
        // Verify that coherence checker catches errors when manually constructed AST is invalid
        use simple_parser::ast::*;

        let impl_block = ImplBlock {
            span: simple_parser::token::Span::new(0, 0, 0, 0),
            attributes: vec![],
            generic_params: vec![],
            where_clause: vec![],
            target_type: Type::Simple("String".to_string()),
            trait_name: Some("Display".to_string()),
            trait_type_params: vec![],
            associated_types: vec![],
            methods: vec![],
        };

        let nodes = vec![Node::Impl(impl_block)];

        let checker = crate::trait_coherence::CoherenceChecker::new();
        let mut checker_mut = checker;
        let errors = checker_mut.check_module(&nodes);

        // Should detect orphan rule violation
        assert!(!errors.is_empty(), "Should detect orphan rule violation");
        assert!(matches!(
            errors[0],
            crate::trait_coherence::CoherenceError::OrphanImpl { .. }
        ));
    }

    // ============== Build Mode and Release Validation Tests (#1034-1035) ==============

    #[test]
    fn test_build_mode_default() {
        let pipeline = CompilerPipeline::new().expect("pipeline ok");
        assert_eq!(pipeline.build_mode(), BuildMode::Debug);
    }

    #[test]
    fn test_build_mode_set() {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");

        pipeline.set_build_mode(BuildMode::Debug);
        assert_eq!(pipeline.build_mode(), BuildMode::Debug);

        pipeline.set_build_mode(BuildMode::Release);
        assert_eq!(pipeline.build_mode(), BuildMode::Release);
    }

    /// Helper to create a project context with test DI profile
    fn create_project_with_test_di_profile() -> crate::project::ProjectContext {
        use crate::di::{DiBindingRule, DiConfig, DiMode, DiProfile, DiScope};
        use std::collections::HashMap;

        let mut profiles = HashMap::new();
        let mut test_profile = DiProfile::default();
        // Add a test binding to simulate active test profile
        test_profile.bindings.push(DiBindingRule {
            predicate: crate::predicate::Predicate::Selector(crate::predicate::Selector::Within("*".to_string())),
            impl_type: "TestLogger".to_string(),
            scope: DiScope::Singleton,
            priority: 0,
            order: 0,
            raw_predicate: "*".to_string(),
        });
        profiles.insert("test".to_string(), test_profile);

        let di_config = DiConfig {
            mode: DiMode::Hybrid,
            profiles,
            concurrent_backend: Default::default(),
        };

        let mut project = crate::project::ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);
        project
    }

    #[test]
    fn test_debug_mode_allows_test_profile() {
        // Debug mode should allow test DI profile
        let source = "main = 42";

        let project = create_project_with_test_di_profile();
        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Debug);

        // Should succeed in debug mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Debug mode should allow test profile");
    }

    #[test]
    fn test_release_mode_rejects_test_profile() {
        // Release mode should reject test DI profile (#1034)
        let source = "main = 42";

        let project = create_project_with_test_di_profile();
        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should fail in release mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_err(), "Release mode should reject test profile");

        match result {
            Err(CompileError::Semantic(ref msg)) => {
                assert!(msg.contains("#1034"), "Error should reference #1034");
                assert!(msg.contains("test"), "Error should mention test profile");
            }
            Err(CompileError::SemanticWithContext(ref p)) => {
                assert!(p.message.contains("#1034"), "Error should reference #1034");
                assert!(p.message.contains("test"), "Error should mention test profile");
            }
            _ => panic!("Expected semantic error with #1034 reference"),
        }
    }

    #[test]
    fn test_debug_mode_allows_runtime_aop() {
        // Debug mode should allow runtime AOP interceptors
        let source = "main = 42";

        // Create a project context with runtime AOP enabled
        use crate::aop_config::AopConfig;
        use crate::project::ProjectContext;

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![],
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.aop_config = Some(aop_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Debug);

        // Should succeed in debug mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Debug mode should allow runtime AOP");
    }

    #[test]
    fn test_release_mode_rejects_runtime_aop() {
        // Release mode should reject runtime AOP interceptors (#1035)
        let source = "main = 42";

        // Create a project context with runtime AOP enabled
        use crate::aop_config::AopConfig;
        use crate::project::ProjectContext;

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![],
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.aop_config = Some(aop_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should fail in release mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_err(), "Release mode should reject runtime AOP");

        match result {
            Err(CompileError::Semantic(ref msg)) => {
                assert!(msg.contains("#1035"), "Error should reference #1035");
                assert!(msg.contains("runtime"), "Error should mention runtime interceptors");
            }
            Err(CompileError::SemanticWithContext(ref p)) => {
                assert!(p.message.contains("#1035"), "Error should reference #1035");
                assert!(
                    p.message.contains("runtime"),
                    "Error should mention runtime interceptors"
                );
            }
            _ => panic!("Expected semantic error with #1035 reference"),
        }
    }

    #[test]
    fn test_release_mode_allows_disabled_runtime_aop() {
        // Release mode should allow runtime_enabled=false
        let source = "main = 42";

        // Create a project context with runtime AOP disabled
        use crate::aop_config::AopConfig;
        use crate::project::ProjectContext;

        let aop_config = AopConfig {
            runtime_enabled: false,
            around: vec![],
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.aop_config = Some(aop_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should succeed when runtime AOP is disabled
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Release mode should allow disabled runtime AOP");
    }

    #[test]
    fn test_release_mode_allows_empty_test_profile() {
        // Release mode should allow empty test profile (no active bindings)
        let source = "main = 42";

        // Create a project context with empty test DI profile
        use crate::di::{DiConfig, DiMode, DiProfile};
        use crate::project::ProjectContext;
        use std::collections::HashMap;

        let mut profiles = HashMap::new();
        profiles.insert("test".to_string(), DiProfile::default()); // Empty profile

        let di_config = DiConfig {
            mode: DiMode::Hybrid,
            profiles,
            concurrent_backend: Default::default(),
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should succeed when test profile has no bindings
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Release mode should allow empty test profile");
    }

    #[test]
    fn simd_report_collects_explicit_loop_requests() {
        let source = "fn main() -> i64:\n    @simd\n    for i in 0..4:\n        pass\n    @simd\n    while false:\n        pass\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_simd_report_lines(&ast_module);

        assert_eq!(lines.len(), 1);
        assert!(lines.iter().any(|line| line.contains("explicit @simd on while-loop")));
        assert!(lines.iter().all(|line| line.contains("not vectorized")));
    }

    #[test]
    fn simd_report_ignores_unannotated_loops() {
        let source = "fn main() -> i64:\n    for i in 0..4:\n        pass\n    while false:\n        pass\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_simd_report_lines(&ast_module);

        assert!(lines.is_empty(), "unexpected SIMD report lines: {lines:?}");
    }

    #[test]
    fn simd_report_detects_auto_vectorization_candidates() {
        let source = "fn main() -> i64:\n    for i in 0..n:\n        out[i] = a[i] + b[i]\n    for j in 0..n:\n        prod[j] = x[j] * y[j]\n    for k in 0..n:\n        mix[k] = a[k] * b[k] + c[k]\n    for m in 0..n:\n        sum += vals[m]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_simd_report_lines(&ast_module);

        assert!(lines.is_empty(), "unexpected AST-only report lines: {lines:?}");
    }

    #[test]
    fn simd_report_explains_explicit_loop_failures() {
        let source = "fn main() -> i64:\n    @simd\n    while false:\n        pass\n    @simd\n    for i, x in items:\n        out[i] = x\n    @simd\n    for j in items:\n        out[j] = src[j]\n    @simd\n    for k in 0..n:\n        a[k] = b[k]\n        c[k] = d[k]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_simd_report_lines(&ast_module);

        assert!(lines.iter().any(|line| line.contains("while-loop; not vectorized: unsupported loop form")));
    }

    #[test]
    fn simd_auto_warns_for_structurally_unsupported_explicit_loops() {
        let source = "fn main() -> i64:\n    @simd\n    while false:\n        pass\n    @simd\n    for i, x in items:\n        out[i] = x\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let lines = pipeline.collect_explicit_simd_warning_lines(&ast_module);

        assert!(lines.iter().any(|line| line.contains("explicit @simd on while-loop was not vectorized")));
        assert!(lines.iter().any(|line| line.contains("explicit @simd on for-loop was not vectorized: unsupported index pattern")));
    }

    #[test]
    fn simd_typed_report_detects_runtime_kernel_lowering_candidates() {
        let source = "fn main() -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    for i in 0..4:\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");
        let hir_module = hir::lower_lenient(&ast_module).expect("hir lower");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_typed_simd_report_lines(&hir_module);

        assert!(lines.iter().any(|line| line.contains("vectorized via runtime kernel rt_numeric_add_f64")));
    }

    #[test]
    fn simd_typed_report_explains_explicit_for_loop_failure() {
        let source = "fn main(n: i64) -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    @simd\n    for i in 0..(n + 1):\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");
        let hir_module = hir::lower_lenient(&ast_module).expect("hir lower");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_typed_simd_report_lines(&hir_module);

        assert!(lines
            .iter()
            .any(|line| line.contains("explicit @simd on for-loop; not vectorized: no typed runtime-kernel lowering available")));
    }

    #[test]
    fn simd_auto_warns_for_typed_explicit_for_loop_failure() {
        let source = "fn main(n: i64) -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    @simd\n    for i in 0..(n + 1):\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");
        let hir_module = hir::lower_lenient(&ast_module).expect("hir lower");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let lines = pipeline.collect_typed_explicit_simd_warning_lines(&hir_module);

        assert!(lines.iter().any(|line| {
            line.contains("warning: function=main: explicit @simd on for-loop was not vectorized")
                && line.contains("no typed runtime-kernel lowering available")
        }));
    }

    #[test]
    fn simd_auto_does_not_warn_for_explicit_loop_that_vectorizes() {
        let source = "fn main() -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    @simd\n    for i in 0..4:\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");
        let hir_module = hir::lower_lenient(&ast_module).expect("hir lower");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);

        assert!(pipeline.collect_explicit_simd_warning_lines(&ast_module).is_empty());
        assert!(pipeline.collect_typed_explicit_simd_warning_lines(&hir_module).is_empty());
    }

    #[test]
    fn simd_auto_lowers_fixed_size_f64_map_add_to_runtime_kernel() {
        let source = "fn main() -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    for i in 0..4:\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_add_f64"))
            }),
            "expected rt_numeric_add_f64 call in MIR"
        );
    }

    #[test]
    fn simd_auto_lowers_fixed_size_f64_map_mul_to_runtime_kernel() {
        let source = "fn main() -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    for i in 0..4:\n        out[i] = a[i] * b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_mul_f64"))
            }),
            "expected rt_numeric_mul_f64 call in MIR"
        );
    }

    #[test]
    fn simd_auto_lowers_fixed_size_f64_map_fma_to_runtime_kernel() {
        let source = "fn main() -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    let c = [9.0, 10.0, 11.0, 12.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    for i in 0..4:\n        out[i] = a[i] * b[i] + c[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_fma_f64"))
            }),
            "expected rt_numeric_fma_f64 call in MIR"
        );
    }

    #[test]
    fn simd_typed_report_detects_dynamic_len_bounded_runtime_kernel_candidate() {
        let source = "fn main(a: [f64], b: [f64], out: [f64]) -> i64:\n    for i in 0..out.len():\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");
        let hir_module = hir::lower_lenient(&ast_module).expect("hir lower");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_typed_simd_report_lines(&hir_module);

        assert!(lines.iter().any(|line| line.contains("vectorized via runtime kernel rt_numeric_add_f64")));
    }

    #[test]
    fn simd_auto_lowers_dynamic_len_bounded_f64_map_add_to_guarded_runtime_kernel() {
        let source =
            "fn main(a: [f64], b: [f64], out: [f64]) -> i64:\n    for i in 0..out.len():\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_add_f64"))
            }),
            "expected guarded rt_numeric_add_f64 call in MIR"
        );
    }

    #[test]
    fn simd_auto_lowers_dynamic_len_bounded_f32_reduction_to_guarded_runtime_kernel() {
        let source = "fn main(vals: [f32]) -> f32:\n    var sum = 0.0f32\n    for i in 0..vals.len():\n        sum = sum + vals[i]\n    return sum\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_sum_f32"))
            }),
            "expected guarded rt_numeric_sum_f32 call in MIR"
        );
    }

    #[test]
    fn simd_auto_lowers_dynamic_len_bounded_f64_reduction_to_guarded_runtime_kernel() {
        let source = "fn main(vals: [f64]) -> f64:\n    var sum = 0.0\n    for i in 0..vals.len():\n        sum = sum + vals[i]\n    return sum\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_sum_f64"))
            }),
            "expected guarded rt_numeric_sum_f64 call in MIR"
        );
    }

    #[test]
    fn simd_typed_report_detects_dynamic_len_bounded_dot_kernel_candidate() {
        let source =
            "fn main(a: [f64], b: [f64]) -> f64:\n    var sum = 0.0\n    for i in 0..a.len():\n        sum = sum + a[i] * b[i]\n    return sum\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");
        let hir_module = hir::lower_lenient(&ast_module).expect("hir lower");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Report);
        let lines = pipeline.collect_typed_simd_report_lines(&hir_module);

        assert!(lines.iter().any(|line| line.contains("vectorized via runtime kernel rt_numeric_dot_f64")));
    }

    #[test]
    fn simd_auto_lowers_dynamic_len_bounded_f64_dot_to_guarded_runtime_kernel() {
        let source =
            "fn main(a: [f64], b: [f64]) -> f64:\n    var sum = 0.0\n    for i in 0..a.len():\n        sum = sum + a[i] * b[i]\n    return sum\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_dot_f64"))
            }),
            "expected guarded rt_numeric_dot_f64 call in MIR"
        );
    }

    #[test]
    fn simd_auto_lowers_dynamic_len_bounded_f32_dot_to_guarded_runtime_kernel() {
        let source =
            "fn main(a: [f32], b: [f32]) -> f32:\n    var sum = 0.0f32\n    for i in 0..a.len():\n        sum = sum + a[i] * b[i]\n    return sum\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Auto);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_dot_f32"))
            }),
            "expected guarded rt_numeric_dot_f32 call in MIR"
        );
    }

    #[test]
    fn simd_off_keeps_fixed_size_f64_map_add_as_scalar_loop() {
        let source = "fn main() -> i64:\n    let a = [1.0, 2.0, 3.0, 4.0]\n    let b = [5.0, 6.0, 7.0, 8.0]\n    var out = [0.0, 0.0, 0.0, 0.0]\n    for i in 0..4:\n        out[i] = a[i] + b[i]\n    return 0\n";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        pipeline.set_simd_mode(SimdMode::Off);
        let mir_module = pipeline.type_check_and_lower(&ast_module).expect("mir lower");

        assert!(
            !mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_add_f64"))
            }),
            "unexpected rt_numeric_add_f64 call in MIR"
        );
        assert!(
            mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(|inst| {
                matches!(inst, mir::MirInst::BinOp { op, .. } if *op == hir::BinOp::Lt)
            }),
            "expected scalar range-loop compare in MIR"
        );
    }

    #[test]
    fn simd_scalar_numeric_builtin_results_unbox_to_native_float() {
        let array_ty = hir::HirType::Array {
            element: hir::TypeId::F32,
            size: Some(4),
        };
        let mut module = hir::HirModule::new();
        let array_ty_id = module.types.register(array_ty);

        let func = hir::HirFunction {
            name: "main".to_string(),
            span: None,
            params: vec![],
            locals: vec![hir::LocalVar {
                name: "vals".to_string(),
                ty: array_ty_id,
                mutability: simple_parser::ast::Mutability::Immutable,
                inject: false,
                is_ghost: false,
            }],
            return_type: hir::TypeId::F32,
            body: vec![hir::HirStmt::Return(Some(hir::HirExpr {
                kind: hir::HirExprKind::BuiltinCall {
                    name: "rt_numeric_sum_f32".to_string(),
                    args: vec![hir::HirExpr {
                        kind: hir::HirExprKind::Local(0),
                        ty: array_ty_id,
                    }],
                },
                ty: hir::TypeId::F32,
            }))],
            visibility: simple_parser::ast::Visibility::Private,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: hir::ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: hir::VerificationMode::default(),
            is_ghost: false,
            is_sync: false,
            has_suspension: false,
        };
        module.functions.push(func);

        let mir_module = mir::lower_to_mir(&module).expect("mir lower");
        assert!(mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(
            |inst| matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name("rt_numeric_sum_f32"))
        ));
        assert!(mir_module.functions.iter().flat_map(|func| &func.blocks).flat_map(|block| &block.instructions).any(
            |inst| matches!(inst, mir::MirInst::UnboxFloat { .. })
        ));
    }
}
