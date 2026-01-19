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
pub mod script_detection;

mod codegen;
mod core;
mod execution;
mod lowering;
mod parsing;

// Re-export main types
pub use core::CompilerPipeline;
pub use execution::{
    generate_smf_bytes, generate_smf_bytes_for_target, generate_smf_from_object, generate_smf_from_object_for_target,
};

// Re-export startup configuration types (#1979, #1986)
pub use module_loader::{extract_startup_config, StartupAppType, StartupConfig, StartupWindowHints};

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

    // ============== Lint Integration Tests ==============

    /// Test helper for running source with a specific lint configuration
    fn run_with_lint_config(source: &str, config: LintConfig) -> Result<Vec<u8>, CompileError> {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        pipeline.set_lint_config(config);
        pipeline.compile_source_to_memory(source)
    }

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

    #[test]
    fn test_debug_mode_allows_test_profile() {
        // Debug mode should allow test DI profile
        let source = "main = 42";

        // Create a project context with test DI profile
        use crate::di::{DiBindingRule, DiConfig, DiMode, DiProfile, DiScope};
        use crate::project::ProjectContext;
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
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);

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

        // Create a project context with test DI profile
        use crate::di::{DiBindingRule, DiConfig, DiMode, DiProfile, DiScope};
        use crate::project::ProjectContext;
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
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should fail in release mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_err(), "Release mode should reject test profile");

        match result {
            Err(CompileError::Semantic(msg)) | Err(CompileError::SemanticWithContext { message: msg, .. }) => {
                assert!(msg.contains("#1034"), "Error should reference #1034");
                assert!(msg.contains("test"), "Error should mention test profile");
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
            Err(CompileError::SemanticWithContext { message: msg, .. }) | Err(CompileError::Semantic(msg)) => {
                assert!(msg.contains("#1035"), "Error should reference #1035");
                assert!(msg.contains("runtime"), "Error should mention runtime interceptors");
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
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should succeed when test profile has no bindings
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Release mode should allow empty test profile");
    }
}
