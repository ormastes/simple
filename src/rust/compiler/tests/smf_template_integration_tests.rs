//! Integration tests for SMF template section writing and reading.

use simple_compiler::smf_writer::generate_smf_with_templates;
use simple_compiler::monomorphize::{GenericTemplates, MonomorphizationMetadata};
use simple_common::target::Target;
use std::collections::HashMap;

// ============================================================================
// SMF Section Tests
// ============================================================================

#[test]
fn test_smf_without_templates() {
    // Empty object code
    let object_code = vec![0x7F, b'E', b'L', b'F']; // Minimal ELF header

    let smf = generate_smf_with_templates(&object_code, None, None, None, Target::host());

    // Should have basic structure but no template sections
    assert!(!smf.is_empty());

    // Verify it's a valid SMF (starts with magic)
    assert_eq!(&smf[0..4], b"SMF\0");
}

#[test]
fn test_smf_with_templates() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    // Create a simple template
    let template_func = create_test_function("identity", vec!["T".to_string()]);
    let templates = GenericTemplates {
        functions: vec![template_func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let metadata = MonomorphizationMetadata::new();

    let smf = generate_smf_with_templates(&object_code, Some(&templates), Some(&metadata), None, Target::host());

    assert!(!smf.is_empty());

    // Should be larger than without templates
    let smf_no_templates = generate_smf_with_templates(&object_code, None, None, None, Target::host());
    assert!(smf.len() > smf_no_templates.len());
}

#[test]
fn test_smf_template_section_magic() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let template_func = create_test_function("identity", vec!["T".to_string()]);
    let templates = GenericTemplates {
        functions: vec![template_func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let smf = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    // TODO: Parse SMF and verify TemplateCode section has GTPL magic
    // This requires SMF parsing support which may not be fully implemented yet

    // For now, just verify the SMF was generated
    assert!(!smf.is_empty());
}

#[test]
fn test_smf_metadata_section() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let mut metadata = MonomorphizationMetadata::new();
    // Add some metadata
    metadata.functions.insert(
        "identity".to_string(),
        simple_compiler::monomorphize::GenericFunctionMeta {
            base_name: "identity".to_string(),
            generic_params: vec!["T".to_string()],
            specializations: vec![],
        },
    );

    let smf = generate_smf_with_templates(&object_code, None, Some(&metadata), None, Target::host());

    assert!(!smf.is_empty());
}

#[test]
fn test_smf_all_generic_constructs() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let templates = GenericTemplates {
        functions: vec![create_test_function("identity", vec!["T".to_string()])],
        structs: vec![create_test_struct("Container", vec!["T".to_string()])],
        classes: vec![create_test_class("Holder", vec!["T".to_string()])],
        enums: vec![create_test_enum("Option", vec!["T".to_string()])],
        traits: vec![create_test_trait("Comparable", vec!["T".to_string()])],
    };

    let smf = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    assert!(!smf.is_empty());

    // Should be significantly larger with all construct types
    let smf_empty = generate_smf_with_templates(&object_code, None, None, None, Target::host());
    assert!(smf.len() > smf_empty.len() + 100); // At least 100 bytes more
}

// ============================================================================
// Serialization Format Tests
// ============================================================================

#[test]
fn test_template_serialization_function() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let mut func = create_test_function("identity", vec!["T".to_string()]);
    func.is_generic_template = true;

    let templates = GenericTemplates {
        functions: vec![func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let smf = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    // TODO: Deserialize and verify function was serialized correctly
    // This requires full deserialization support (Phase 3 TODO)

    assert!(!smf.is_empty());
}

#[test]
fn test_template_serialization_multiple_params() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let func = create_test_function("pair", vec!["T".to_string(), "U".to_string()]);

    let templates = GenericTemplates {
        functions: vec![func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let smf = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    assert!(!smf.is_empty());
}

#[test]
fn test_metadata_serialization() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let mut metadata = MonomorphizationMetadata::new();

    // Add function metadata
    metadata.functions.insert(
        "square".to_string(),
        simple_compiler::monomorphize::GenericFunctionMeta {
            base_name: "square".to_string(),
            generic_params: vec!["T".to_string()],
            specializations: vec![simple_compiler::monomorphize::SpecializationEntry {
                type_args: vec![simple_compiler::monomorphize::ConcreteType::Int],
                mangled_name: "square$Int".to_string(),
                bindings: HashMap::new(),
            }],
        },
    );

    let smf = generate_smf_with_templates(&object_code, None, Some(&metadata), None, Target::host());

    // TODO: Deserialize and verify metadata
    assert!(!smf.is_empty());
}

// ============================================================================
// Symbol Table Tests
// ============================================================================

#[test]
#[ignore] // Requires SMF symbol table parsing
fn test_symbol_table_template_marker() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let func = create_test_function("identity", vec!["T".to_string()]);
    let templates = GenericTemplates {
        functions: vec![func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let smf_bytes = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    // TODO: Parse SMF and check symbol table
    // let smf = parse_smf(&smf_bytes).unwrap();
    // let symbol = smf.find_symbol("identity").unwrap();
    // assert!(symbol.flags & GENERIC_TEMPLATE != 0);
    // assert_eq!(symbol.template_param_count, 1);
}

// ============================================================================
// Backward Compatibility Tests
// ============================================================================

#[test]
fn test_smf_backward_compatible() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    // Old-style SMF (no templates)
    let smf_old = generate_smf_with_templates(&object_code, None, None, None, Target::host());

    // New-style SMF (with templates)
    let func = create_test_function("identity", vec!["T".to_string()]);
    let templates = GenericTemplates {
        functions: vec![func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };
    let smf_new = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    // Both should have valid SMF magic
    assert_eq!(&smf_old[0..4], b"SMF\0");
    assert_eq!(&smf_new[0..4], b"SMF\0");

    // New should be larger (has template sections)
    assert!(smf_new.len() > smf_old.len());
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_empty_templates_object() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let templates = GenericTemplates {
        functions: vec![],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    // Empty templates should fall back to no-template path
    let smf = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    let smf_no_templates = generate_smf_with_templates(&object_code, None, None, None, Target::host());

    // Should be roughly the same size (no actual templates)
    assert!((smf.len() as i64 - smf_no_templates.len() as i64).abs() < 100);
}

#[test]
fn test_large_template_set() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    // Create many templates
    let mut functions = Vec::new();
    for i in 0..20 {
        functions.push(create_test_function(&format!("func{}", i), vec!["T".to_string()]));
    }

    let templates = GenericTemplates {
        functions,
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let smf = generate_smf_with_templates(&object_code, Some(&templates), None, None, Target::host());

    // Should successfully generate even with many templates
    assert!(!smf.is_empty());
}

// ============================================================================
// Cross-Platform Tests
// ============================================================================

#[test]
fn test_smf_target_x86_64() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let func = create_test_function("identity", vec!["T".to_string()]);
    let templates = GenericTemplates {
        functions: vec![func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let smf = generate_smf_with_templates(
        &object_code,
        Some(&templates),
        None,
        None,
        Target::parse("x86_64-linux").unwrap(),
    );

    assert!(!smf.is_empty());
    // TODO: Verify platform field in header
}

#[test]
fn test_smf_target_aarch64() {
    let object_code = vec![0x7F, b'E', b'L', b'F'];

    let func = create_test_function("identity", vec!["T".to_string()]);
    let templates = GenericTemplates {
        functions: vec![func],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let smf = generate_smf_with_templates(
        &object_code,
        Some(&templates),
        None,
        None,
        Target::parse("aarch64-macos").unwrap(),
    );

    assert!(!smf.is_empty());
}

// ============================================================================
// Helper Functions
// ============================================================================

fn create_test_function(name: &str, generic_params: Vec<String>) -> simple_parser::ast::FunctionDef {
    use simple_parser::ast::Visibility;
    use simple_parser::token::Span;

    simple_parser::ast::FunctionDef {
        name: name.to_string(),
        generic_params: generic_params.clone(),
        params: vec![],
        return_type: None,
        body: simple_parser::ast::Block::default(),
        is_generic_template: !generic_params.is_empty(),
        specialization_of: None,
        type_bindings: HashMap::new(),
        attributes: vec![],
        where_clause: vec![],
        effects: vec![],
        contract: None,
        span: Span::new(0, 0, 0, 0),
        visibility: Visibility::Public,
        decorators: vec![],
        doc_comment: None,
        is_abstract: false,
        is_sync: false,
        bounds_block: None,
        is_me_method: false,
        return_constraint: None,
    }
}

fn create_test_struct(name: &str, generic_params: Vec<String>) -> simple_parser::ast::StructDef {
    use simple_parser::ast::Visibility;
    use simple_parser::token::Span;

    simple_parser::ast::StructDef {
        name: name.to_string(),
        generic_params: generic_params.clone(),
        fields: vec![],
        methods: vec![],
        is_generic_template: !generic_params.is_empty(),
        specialization_of: None,
        type_bindings: HashMap::new(),
        where_clause: vec![],
        attributes: vec![],
        invariant: None,
        span: Span::new(0, 0, 0, 0),
        visibility: Visibility::Public,
        doc_comment: None,
    }
}

fn create_test_class(name: &str, generic_params: Vec<String>) -> simple_parser::ast::ClassDef {
    use simple_parser::ast::Visibility;
    use simple_parser::token::Span;

    simple_parser::ast::ClassDef {
        name: name.to_string(),
        generic_params: generic_params.clone(),
        fields: vec![],
        methods: vec![],
        is_generic_template: !generic_params.is_empty(),
        specialization_of: None,
        type_bindings: HashMap::new(),
        where_clause: vec![],
        attributes: vec![],
        parent: None,
        mixins: vec![],
        invariant: None,
        effects: vec![],
        macro_invocations: vec![],
        span: Span::new(0, 0, 0, 0),
        visibility: Visibility::Public,
        doc_comment: None,
    }
}

fn create_test_enum(name: &str, generic_params: Vec<String>) -> simple_parser::ast::EnumDef {
    use simple_parser::ast::Visibility;
    use simple_parser::token::Span;

    simple_parser::ast::EnumDef {
        name: name.to_string(),
        generic_params: generic_params.clone(),
        variants: vec![],
        methods: vec![],
        is_generic_template: !generic_params.is_empty(),
        specialization_of: None,
        type_bindings: HashMap::new(),
        where_clause: vec![],
        attributes: vec![],
        span: Span::new(0, 0, 0, 0),
        visibility: Visibility::Public,
        doc_comment: None,
    }
}

fn create_test_trait(name: &str, generic_params: Vec<String>) -> simple_parser::ast::TraitDef {
    use simple_parser::ast::{Visibility};
    use simple_parser::token::Span;

    simple_parser::ast::TraitDef {
        name: name.to_string(),
        generic_params: generic_params.clone(),
        methods: vec![],
        super_traits: vec![],
        associated_types: vec![],
        where_clause: vec![],
        is_generic_template: !generic_params.is_empty(),
        specialization_of: None,
        type_bindings: HashMap::new(),
        span: Span::new(0, 0, 0, 0),
        visibility: Visibility::Public,
        doc_comment: None,
    }
}
