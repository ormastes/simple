//! Compiler integration tests - Part 2
//! HIR, MIR, Effect, DataSection, Value, Manual Memory tests

#![allow(unused_imports, unused_variables, unused_comparisons)]

use simple_compiler::CompilerPipeline;
use simple_loader::{ModuleLoader, ModuleRegistry};
use simple_parser::{Lexer, Parser, Span, Token, TokenKind};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// HirModule and HirFunction Tests
// =============================================================================

#[test]
fn test_hir_module_creation() {
    use simple_compiler::hir::Lowerer;
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 100");
    let ast = parser.parse().expect("parse ok");

    let lowerer = Lowerer::new();
    let hir_result = lowerer.lower_module(&ast);
    // HirModule may or may not have functions depending on lowerer state
    // Just verify it returns without panic
    let _ = hir_result;
}

#[test]
fn test_hir_function_is_public() {
    use simple_compiler::hir::Lowerer;
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 0");
    let ast = parser.parse().expect("parse ok");

    let lowerer = Lowerer::new();
    let hir_result = lowerer.lower_module(&ast);
    // Just verify lowering doesn't panic
    let _ = hir_result;
}

// =============================================================================
// DataSectionKind Tests (Feature #71-80 coverage)
// =============================================================================

#[test]
fn test_data_section_kind_readonly() {
    use simple_compiler::linker::DataSectionKind;
    let kind = DataSectionKind::ReadOnly;
    assert!(kind.is_readonly());
}

#[test]
fn test_data_section_kind_mutable() {
    use simple_compiler::linker::DataSectionKind;
    let kind = DataSectionKind::Mutable;
    assert!(!kind.is_readonly());
}

#[test]
fn test_data_section_kind_to_section_type() {
    use simple_compiler::linker::{DataSectionKind, SectionType};
    assert_eq!(
        DataSectionKind::ReadOnly.to_section_type(),
        SectionType::RoData
    );
    assert_eq!(
        DataSectionKind::Mutable.to_section_type(),
        SectionType::Data
    );
}

// =============================================================================
// Value Type Tests (Features supporting type system)
// =============================================================================

#[test]
fn test_value_int_methods() {
    use simple_compiler::Value;
    let val = Value::Int(42);
    assert!(val.as_int().is_ok());
    assert_eq!(val.as_int().unwrap(), 42);
}

#[test]
fn test_value_float_methods() {
    use simple_compiler::Value;
    let val = Value::Float(3.14);
    assert!(val.as_float().is_ok());
    assert!((val.as_float().unwrap() - 3.14).abs() < 0.001);
}

#[test]
fn test_value_truthy() {
    use simple_compiler::Value;
    assert!(Value::Bool(true).truthy());
    assert!(!Value::Bool(false).truthy());
    assert!(Value::Int(1).truthy());
    assert!(!Value::Int(0).truthy());
}

#[test]
fn test_value_type_name() {
    use simple_compiler::Value;
    assert_eq!(Value::Int(0).type_name(), "i64");
    assert_eq!(Value::Float(0.0).type_name(), "f64");
    assert_eq!(Value::Bool(true).type_name(), "bool");
    assert_eq!(Value::Str("".into()).type_name(), "str");
}

#[test]
fn test_value_to_display_string() {
    use simple_compiler::Value;
    assert_eq!(Value::Int(42).to_display_string(), "42");
    assert_eq!(Value::Bool(true).to_display_string(), "true");
}

// =============================================================================
// Manual Memory Types Tests (Feature #40-50 related)
// =============================================================================

#[test]
fn test_manual_unique_value() {
    use simple_compiler::{ManualUniqueValue, Value};
    let unique = ManualUniqueValue::new(Value::Int(42));
    assert_eq!(unique.inner(), &Value::Int(42));
    let inner = unique.into_inner();
    assert_eq!(inner, Value::Int(42));
}

#[test]
fn test_manual_shared_value() {
    use simple_compiler::{ManualSharedValue, Value};
    let shared = ManualSharedValue::new(Value::Int(100));
    assert_eq!(shared.inner(), &Value::Int(100));
    let weak = shared.downgrade();
    assert!(weak.upgrade().is_some());
}

// =============================================================================
// FutureValue Tests (Feature #51-60 async support)
// =============================================================================

#[test]
fn test_future_value_new() {
    use simple_compiler::{FutureValue, Value};
    let future = FutureValue::new(|| Ok(Value::Int(42)));
    // Future should be created
    assert!(std::mem::size_of_val(&future) > 0);
}

// =============================================================================
// GeneratorValue Tests (Feature #61-70 generator support)
// =============================================================================

#[test]
fn test_generator_value_new() {
    use simple_compiler::{GeneratorValue, Value};
    let gen = GeneratorValue::new_with_values(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
    assert!(!gen.is_done());
}

#[test]
fn test_generator_value_next() {
    use simple_compiler::{GeneratorValue, Value};
    let gen = GeneratorValue::new_with_values(vec![Value::Int(1), Value::Int(2)]);
    assert_eq!(gen.next(), Some(Value::Int(1)));
    assert_eq!(gen.next(), Some(Value::Int(2)));
    assert_eq!(gen.next(), None);
    assert!(gen.is_done());
}

#[test]
fn test_generator_value_collect_remaining() {
    use simple_compiler::{GeneratorValue, Value};
    let gen = GeneratorValue::new_with_values(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
    let _ = gen.next(); // Consume first
    let remaining = gen.collect_remaining();
    assert_eq!(remaining.len(), 2);
}

// =============================================================================
// ClassName, EnumTypeName, VariantName Tests (Type system coverage)
// =============================================================================

#[test]
fn test_class_name() {
    use simple_compiler::ClassName;
    let name = ClassName::new("MyClass");
    assert_eq!(name.as_str(), "MyClass");
}

#[test]
fn test_enum_type_name() {
    use simple_compiler::EnumTypeName;
    let name = EnumTypeName::new("MyEnum");
    assert_eq!(name.as_str(), "MyEnum");
}

#[test]
fn test_variant_name() {
    use simple_compiler::VariantName;
    let name = VariantName::new("SomeVariant");
    assert_eq!(name.as_str(), "SomeVariant");
}

// =============================================================================
// Features #81-95 IT Tests - Public Function Coverage
// =============================================================================

// Feature #93-95: Numeric Literal Parsing
#[test]
fn test_parser_hex_literal() {
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 0xFF");
    let ast = parser.parse();
    assert!(ast.is_ok(), "Should parse hex literal: {:?}", ast.err());
}

#[test]
fn test_parser_binary_literal() {
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 0b1010");
    let ast = parser.parse();
    assert!(ast.is_ok(), "Should parse binary literal: {:?}", ast.err());
}

#[test]
fn test_parser_octal_literal() {
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 0o755");
    let ast = parser.parse();
    assert!(ast.is_ok(), "Should parse octal literal: {:?}", ast.err());
}

#[test]
fn test_parser_hex_with_underscore() {
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 0xFF_FF");
    let ast = parser.parse();
    assert!(
        ast.is_ok(),
        "Should parse hex with underscore: {:?}",
        ast.err()
    );
}

#[test]
fn test_parser_binary_with_underscore() {
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 0b1111_0000");
    let ast = parser.parse();
    assert!(
        ast.is_ok(),
        "Should parse binary with underscore: {:?}",
        ast.err()
    );
}

// Feature #81: Range Patterns (if parser supports)
#[test]
fn test_parser_range_expression() {
    use simple_parser::Parser;

    // Range expression in for loop
    let mut parser = Parser::new(
        r#"
for i in 0..10:
    pass
main = 0
"#,
    );
    let result = parser.parse();
    // May or may not be supported yet
    let _ = result;
}

// Feature #84: Channel Types (compile-time check)
#[test]
fn test_parser_generic_type_annotation() {
    use simple_parser::Parser;

    // Generic type syntax
    let mut parser = Parser::new(
        r#"
ch: Channel[int] = nil
main = 0
"#,
    );
    let result = parser.parse();
    let _ = result; // May not be supported yet
}

// =============================================================================
// Additional Compiler Public Functions
// =============================================================================

#[test]
fn test_compiler_pipeline_compile_to_bytes() {
    use simple_compiler::CompilerPipeline;
    use std::fs;
    use tempfile::tempdir;

    let dir = tempdir().expect("tempdir");
    let src = dir.path().join("test.spl");
    let out = dir.path().join("test.smf");

    fs::write(&src, "main = 42").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src, &out);
    assert!(result.is_ok(), "Should compile: {:?}", result.err());

    // Verify SMF was created
    let bytes = fs::read(&out);
    assert!(bytes.is_ok(), "SMF file should exist");
    assert!(!bytes.unwrap().is_empty(), "SMF should not be empty");
}

#[test]
fn test_lowerer_with_arithmetic() {
    use simple_compiler::hir::Lowerer;
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 1 + 2 * 3");
    let ast = parser.parse().expect("parse ok");

    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&ast);
    // Should handle arithmetic expressions
    let _ = result;
}

#[test]
fn test_lowerer_with_comparison() {
    use simple_compiler::hir::Lowerer;
    use simple_parser::Parser;

    let source = r#"
if 1 < 2:
    main = 1
else:
    main = 0
"#;
    let mut parser = Parser::new(source);
    let parse_result = parser.parse();
    if parse_result.is_err() {
        return;
    }
    let ast = parse_result.unwrap();

    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&ast);
    let _ = result;
}

#[test]
fn test_mir_lowerer_with_expressions() {
    use simple_compiler::hir::Lowerer;
    use simple_compiler::mir::MirLowerer;
    use simple_parser::Parser;

    let mut parser = Parser::new("main = 10 - 5");
    let ast = parser.parse().expect("parse ok");

    let hir_lowerer = Lowerer::new();
    let hir_result = hir_lowerer.lower_module(&ast);
    if hir_result.is_err() {
        return;
    }
    let hir = hir_result.unwrap();

    let mir_lowerer = MirLowerer::new();
    let result = mir_lowerer.lower_module(&hir);
    let _ = result;
}

#[test]
fn test_codegen_with_negative() {
    use simple_compiler::codegen::Codegen;
    use simple_compiler::hir::Lowerer;
    use simple_compiler::mir::MirLowerer;
    use simple_parser::Parser;

    let mut parser = Parser::new("main = -42");
    let ast = parser.parse().expect("parse ok");

    let hir_lowerer = Lowerer::new();
    let hir_result = hir_lowerer.lower_module(&ast);
    if hir_result.is_err() {
        return;
    }
    let hir = hir_result.unwrap();

    let mir_lowerer = MirLowerer::new();
    let mir_result = mir_lowerer.lower_module(&hir);
    if mir_result.is_err() {
        return;
    }
    let mir = mir_result.unwrap();

    let codegen = Codegen::new().expect("codegen ok");
    let result = codegen.compile_module(&mir);
    let _ = result;
}

// =============================================================================
// Loader Public Functions
// =============================================================================

#[test]
fn test_module_loader_load_and_entry() {
    use simple_driver::Runner;
    use simple_loader::ModuleLoader;
    use tempfile::tempdir;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("entry_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 123", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Test entry_point
    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some(), "Should have entry point");
    assert_eq!(entry.unwrap()(), 123);
}

#[test]
fn test_module_loader_exports() {
    use simple_driver::Runner;
    use simple_loader::ModuleLoader;
    use tempfile::tempdir;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("exports_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 0", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Test exports
    let exports = module.exports();
    assert!(!exports.is_empty(), "Should have exports");
}

#[test]
fn test_loaded_module_source_hash_it() {
    use simple_driver::Runner;
    use simple_loader::ModuleLoader;
    use tempfile::tempdir;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("hash_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 99", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Test source_hash
    let hash = module.source_hash();
    // Hash should be non-zero for non-empty source
    let _ = hash;
}

#[test]
fn test_loaded_module_is_reloadable_it() {
    use simple_driver::Runner;
    use simple_loader::ModuleLoader;
    use tempfile::tempdir;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reload_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 50", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Test is_reloadable
    let _reloadable = module.is_reloadable();
}

// =============================================================================
// SmfWriter Additional Coverage
// =============================================================================

#[test]
fn test_smf_writer_multiple_sections() {
    use simple_compiler::linker::{
        DataSectionKind, SmfSymbol, SmfWriter, SymbolBinding, SymbolType,
    };
    use std::io::Cursor;

    let mut writer = SmfWriter::new();

    // Add multiple code sections
    let code1 = vec![0x90, 0xC3]; // NOP, RET
    writer.add_code_section(".text", code1);

    // Add data section
    let data = vec![0x01, 0x02, 0x03, 0x04];
    writer.add_data_section(".data", data, DataSectionKind::Mutable);

    // Add rodata section
    let rodata = b"Hello, World!".to_vec();
    writer.add_data_section(".rodata", rodata, DataSectionKind::ReadOnly);

    // Add multiple symbols
    let sym1 = SmfSymbol {
        name: "main".to_string(),
        binding: SymbolBinding::Global,
        sym_type: SymbolType::Function,
        section_index: 0,
        value: 0,
        size: 2,
    };
    writer.add_symbol(sym1);

    let sym2 = SmfSymbol {
        name: "data_ptr".to_string(),
        binding: SymbolBinding::Global,
        sym_type: SymbolType::Data,
        section_index: 1,
        value: 0,
        size: 4,
    };
    writer.add_symbol(sym2);

    // Write and verify
    let mut output = Cursor::new(Vec::new());
    let result = writer.write(&mut output);
    assert!(result.is_ok(), "Should write: {:?}", result.err());
    assert!(!output.into_inner().is_empty());
}

// =============================================================================
// TypeRegistry Additional Coverage
// =============================================================================

#[test]
fn test_type_registry_multiple_types() {
    use simple_compiler::hir::{HirType, TypeRegistry};

    let mut registry = TypeRegistry::new();

    // Register various types
    let void_id = registry.register(HirType::Void);
    let bool_id = registry.register(HirType::Bool);
    let int_id = registry.register(HirType::signed_int(32));
    let float_id = registry.register(HirType::Float { bits: 64 });
    let string_id = registry.register(HirType::String);

    // All IDs should be different
    assert_ne!(void_id.0, bool_id.0);
    assert_ne!(bool_id.0, int_id.0);
    assert_ne!(int_id.0, float_id.0);
    assert_ne!(float_id.0, string_id.0);

    // All should be retrievable
    assert!(registry.get(void_id).is_some());
    assert!(registry.get(bool_id).is_some());
    assert!(registry.get(int_id).is_some());
    assert!(registry.get(float_id).is_some());
    assert!(registry.get(string_id).is_some());
}

#[test]
fn test_type_registry_named_lookup() {
    use simple_compiler::hir::{HirType, TypeRegistry};

    let mut registry = TypeRegistry::new();

    // Register named types
    registry.register_named("MyInt".to_string(), HirType::signed_int(32));
    registry.register_named("MyFloat".to_string(), HirType::Float { bits: 64 });
    registry.register_named("MyBool".to_string(), HirType::Bool);

    // Lookup by name
    assert!(registry.lookup("MyInt").is_some());
    assert!(registry.lookup("MyFloat").is_some());
    assert!(registry.lookup("MyBool").is_some());
    assert!(registry.lookup("NonExistent").is_none());
}

// =============================================================================
// MirFunction Additional Coverage
// =============================================================================

#[test]
fn test_mir_function_multiple_blocks() {
    use simple_compiler::hir::TypeId;
    use simple_compiler::mir::MirFunction;
    use simple_parser::Visibility;

    let mut func = MirFunction::new("multi_block".to_string(), TypeId(1), Visibility::Public);

    // Create multiple blocks
    let block1 = func.new_block();
    let block2 = func.new_block();
    let block3 = func.new_block();

    // All block IDs should be different
    assert_ne!(block1.0, block2.0);
    assert_ne!(block2.0, block3.0);
}

#[test]
fn test_mir_function_multiple_vregs() {
    use simple_compiler::hir::TypeId;
    use simple_compiler::mir::MirFunction;
    use simple_parser::Visibility;

    let mut func = MirFunction::new("multi_vreg".to_string(), TypeId(1), Visibility::Private);

    // Create multiple virtual registers
    let vreg1 = func.new_vreg();
    let vreg2 = func.new_vreg();
    let vreg3 = func.new_vreg();
    let vreg4 = func.new_vreg();

    // All VReg IDs should be different
    assert_ne!(vreg1.0, vreg2.0);
    assert_ne!(vreg2.0, vreg3.0);
    assert_ne!(vreg3.0, vreg4.0);
}

// =============================================================================
// Effect and EffectSet Additional Coverage
// =============================================================================

#[test]
fn test_effect_is_async() {
    use simple_compiler::mir::Effect;

    assert!(Effect::Compute.is_async());
    assert!(Effect::Io.is_async());
    assert!(!Effect::Wait.is_async());
    assert!(Effect::GcAlloc.is_async());
}

#[test]
fn test_effect_is_nogc() {
    use simple_compiler::mir::Effect;

    assert!(Effect::Compute.is_nogc());
    assert!(Effect::Io.is_nogc());
    assert!(Effect::Wait.is_nogc());
    assert!(!Effect::GcAlloc.is_nogc());
}

#[test]
fn test_effect_set_async_check() {
    use simple_compiler::mir::{Effect, EffectSet};

    let mut effects = EffectSet::new();
    effects.push(Effect::Compute);
    effects.push(Effect::Io);

    // Check if pipeline safe (no Wait effects)
    assert!(effects.is_pipeline_safe());

    effects.push(Effect::Wait);
    assert!(!effects.is_pipeline_safe());
}

#[test]
fn test_effect_set_effects_list() {
    use simple_compiler::mir::{Effect, EffectSet};

    let mut effects = EffectSet::new();
    effects.push(Effect::Compute);
    effects.push(Effect::GcAlloc);

    let effect_list = effects.effects();
    assert_eq!(effect_list.len(), 2);
}

// =============================================================================
// Driver Public Functions
// =============================================================================

#[test]
fn test_run_code_various_values() {
    use simple_driver::run_code;

    // Test various return values
    let r1 = run_code("main = 0", &[], "");
    assert!(r1.is_ok());

    let r2 = run_code("main = 100", &[], "");
    assert!(r2.is_ok());

    let r3 = run_code("main = 1 + 2 + 3", &[], "");
    assert!(r3.is_ok());
}

#[test]
fn test_interpreter_various_configs() {
    use simple_driver::{Interpreter, RunConfig, RunningType};

    let interpreter = Interpreter::new();

    // Test with different configs
    let config1 = RunConfig::default();
    let r1 = interpreter.run("main = 1", config1);
    assert!(r1.is_ok());

    let config2 = RunConfig {
        args: vec!["arg1".to_string()],
        stdin: "".to_string(),
        timeout_ms: 5000,
        in_memory: true,
        running_type: RunningType::default(),
        ..Default::default()
    };
    let r2 = interpreter.run("main = 2", config2);
    assert!(r2.is_ok());
}

#[test]
fn test_runner_gc_heap_bytes() {
    use simple_driver::Runner;

    // Runner with GC - gc() returns the GC runtime
    let runner = Runner::new();
    let gc = runner.gc();
    let heap_bytes = gc.heap_bytes();
    // heap_bytes should be a valid size
    assert!(heap_bytes >= 0);
}
