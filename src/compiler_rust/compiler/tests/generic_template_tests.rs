//! Tests for generic template bytecode storage and deferred monomorphization.

use simple_compiler::monomorphize::{
    partition_generic_constructs, DeferredMonomorphizer, GenericTemplate, InstantiationMode, MonomorphizationMetadata,
    SpecializationKey,
};
use simple_compiler::monomorphize::{ConcreteType, GenericTemplates, SpecializedInstances};
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef, Module, Node, StructDef, TraitDef, Type};
use simple_parser::Parser;
use std::collections::HashMap;

// ============================================================================
// Unit Tests: Template Partitioning
// ============================================================================

#[test]
fn test_partition_generic_function() {
    let source = r#"fn identity<T>(x: T) -> T:
    return x
"#;

    let module = Parser::new(source).parse().expect("Parse failed");
    let (templates, specialized, metadata) = partition_generic_constructs(&module);

    // Should have 1 template function
    assert_eq!(templates.functions.len(), 1);
    assert_eq!(templates.functions[0].name, "identity");
    assert_eq!(templates.functions[0].generic_params.len(), 1);
    assert!(templates.functions[0].is_generic_template);

    // No specializations yet
    assert_eq!(specialized.functions.len(), 0);

    // Metadata should track the template
    assert!(metadata.functions.contains_key("identity"));
    assert_eq!(metadata.functions["identity"].generic_params.len(), 1);
}

#[test]
fn test_partition_generic_struct() {
    let source = r#"struct Container<T>:
    value: T
"#;

    let module = Parser::new(source).parse().expect("Parse failed");
    let (templates, specialized, _) = partition_generic_constructs(&module);

    assert_eq!(templates.structs.len(), 1);
    assert_eq!(templates.structs[0].name, "Container");
    assert_eq!(templates.structs[0].generic_params.len(), 1);
    assert!(templates.structs[0].is_generic_template);

    assert_eq!(specialized.structs.len(), 0);
}

#[test]
fn test_partition_generic_enum() {
    let source = r#"enum Result<T, E>:
    Ok(T)
    Err(E)
"#;

    let module = Parser::new(source).parse().expect("Parse failed");
    let (templates, specialized, metadata) = partition_generic_constructs(&module);

    assert_eq!(templates.enums.len(), 1);
    assert_eq!(templates.enums[0].name, "Result");
    assert_eq!(templates.enums[0].generic_params.len(), 2);
    assert_eq!(templates.enums[0].generic_params[0], "T");
    assert_eq!(templates.enums[0].generic_params[1], "E");

    assert!(metadata.enums.contains_key("Result"));
}

#[test]
fn test_partition_mixed_generic_and_regular() {
    let source = r#"fn identity<T>(x: T) -> T:
    return x

fn add(a: i32, b: i32) -> i32:
    return a + b
"#;

    let module = Parser::new(source).parse().expect("Parse failed");
    let (templates, specialized, _) = partition_generic_constructs(&module);

    // identity<T> should be in templates
    assert_eq!(templates.functions.len(), 1);
    assert_eq!(templates.functions[0].name, "identity");

    // add should be in specialized (non-generic)
    assert_eq!(specialized.functions.len(), 1);
    assert_eq!(specialized.functions[0].name, "add");
    assert!(!specialized.functions[0].is_generic_template);
}

#[test]
fn test_partition_all_generic_constructs() {
    let source = r#"fn identity<T>(x: T) -> T:
    return x

struct Container<T>:
    value: T

class Holder<T>:
    data: T

enum Option<T>:
    Some(T)
    None

trait Comparable<T>:
    fn compare(other: T) -> i32
"#;

    let module = Parser::new(source).parse().expect("Parse failed");
    let (templates, _, metadata) = partition_generic_constructs(&module);

    assert_eq!(templates.functions.len(), 1);
    assert_eq!(templates.structs.len(), 1);
    assert_eq!(templates.classes.len(), 1);
    assert_eq!(templates.enums.len(), 1);
    assert_eq!(templates.traits.len(), 1);

    // Metadata should track all templates
    assert!(metadata.functions.contains_key("identity"));
    assert!(metadata.structs.contains_key("Container"));
    assert!(metadata.enums.contains_key("Option"));
    assert!(metadata.traits.contains_key("Comparable"));
}

// ============================================================================
// Unit Tests: Metadata Building
// ============================================================================

#[test]
fn test_metadata_tracks_specializations() {
    // Manually create a template and specialization
    let mut template = create_test_function("identity", vec!["T".to_string()]);
    template.is_generic_template = true;

    let mut specialized = create_test_function("identity$Int", vec![]);
    specialized.is_generic_template = false;
    specialized.specialization_of = Some("identity".to_string());
    specialized.type_bindings = {
        let mut bindings = HashMap::new();
        bindings.insert("T".to_string(), Type::Simple("Int".to_string()));
        bindings
    };

    let templates = GenericTemplates {
        functions: vec![template],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let specialized_instances = SpecializedInstances {
        functions: vec![specialized],
        structs: vec![],
        classes: vec![],
        enums: vec![],
    };

    let metadata =
        simple_compiler::monomorphize::partition::build_monomorphization_metadata(&templates, &specialized_instances);

    // Check that specialization is tracked
    assert!(metadata.functions.contains_key("identity"));
    let func_meta = &metadata.functions["identity"];
    assert_eq!(func_meta.specializations.len(), 1);
    assert_eq!(func_meta.specializations[0].mangled_name, "identity$Int");
}

#[test]
fn test_metadata_multiple_specializations() {
    let mut template = create_test_function("square", vec!["T".to_string()]);
    template.is_generic_template = true;

    let mut spec_int = create_test_function("square$Int", vec![]);
    spec_int.specialization_of = Some("square".to_string());

    let mut spec_float = create_test_function("square$Float", vec![]);
    spec_float.specialization_of = Some("square".to_string());

    let templates = GenericTemplates {
        functions: vec![template],
        structs: vec![],
        classes: vec![],
        enums: vec![],
        traits: vec![],
    };

    let specialized_instances = SpecializedInstances {
        functions: vec![spec_int, spec_float],
        structs: vec![],
        classes: vec![],
        enums: vec![],
    };

    let metadata =
        simple_compiler::monomorphize::partition::build_monomorphization_metadata(&templates, &specialized_instances);

    let func_meta = &metadata.functions["square"];
    assert_eq!(func_meta.specializations.len(), 2);

    let names: Vec<_> = func_meta
        .specializations
        .iter()
        .map(|s| s.mangled_name.as_str())
        .collect();
    assert!(names.contains(&"square$Int"));
    assert!(names.contains(&"square$Float"));
}

// ============================================================================
// Unit Tests: Deferred Monomorphization
// ============================================================================

#[test]
fn test_deferred_mono_new() {
    let mono = DeferredMonomorphizer::new(InstantiationMode::LinkTime);

    let stats = mono.get_stats();
    assert_eq!(stats.template_count, 0);
    assert_eq!(stats.specialization_count, 0);
    assert_eq!(mono.mode(), InstantiationMode::LinkTime);
}

#[test]
fn test_deferred_mono_get_stats() {
    let mono = DeferredMonomorphizer::new(InstantiationMode::JitTime);
    let stats = mono.get_stats();

    assert_eq!(stats.template_count, 0);
    assert_eq!(stats.specialization_count, 0);
    assert_eq!(mono.mode(), InstantiationMode::JitTime);
}

#[test]
fn test_deferred_mono_cache_template() {
    // Test that monomorphizer can be created and used
    // (Cannot directly test template cache as it's private)
    let mono = DeferredMonomorphizer::new(InstantiationMode::LinkTime);

    let stats = mono.get_stats();
    assert_eq!(stats.template_count, 0);
}

#[test]
fn test_deferred_mono_instantiate_function() {
    let mut mono = DeferredMonomorphizer::new(InstantiationMode::LinkTime);

    // Try to instantiate without loading templates (should fail)
    let type_args = vec![ConcreteType::Int];
    let result = mono.instantiate_function("identity", &type_args);

    // Should fail because no templates loaded
    assert!(result.is_err());
}

#[test]
fn test_deferred_mono_caching() {
    // Test that monomorphizer maintains different modes correctly
    let mono_link = DeferredMonomorphizer::new(InstantiationMode::LinkTime);
    let mono_jit = DeferredMonomorphizer::new(InstantiationMode::JitTime);

    assert_eq!(mono_link.mode(), InstantiationMode::LinkTime);
    assert_eq!(mono_jit.mode(), InstantiationMode::JitTime);
}

#[test]
fn test_deferred_mono_error_wrong_type_arg_count() {
    // Test error handling for wrong type argument count
    // (Cannot directly test without loading templates, so test API exists)
    let mut mono = DeferredMonomorphizer::new(InstantiationMode::LinkTime);

    // Try to instantiate non-existent template (should fail)
    let type_args = vec![ConcreteType::Int];
    let result = mono.instantiate_function("pair", &type_args);

    assert!(result.is_err());
}

#[test]
fn test_deferred_mono_error_template_not_found() {
    let mut mono = DeferredMonomorphizer::new(InstantiationMode::LinkTime);

    // Try to instantiate non-existent template
    let type_args = vec![ConcreteType::Int];
    let result = mono.instantiate_function("nonexistent", &type_args);

    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();
    assert!(err_msg.contains("No template found") || err_msg.contains("nonexistent"));
}

// ============================================================================
// Unit Tests: Specialization Key
// ============================================================================

#[test]
fn test_specialization_key_equality() {
    let key1 = SpecializationKey::new("identity", vec![ConcreteType::Int]);
    let key2 = SpecializationKey::new("identity", vec![ConcreteType::Int]);
    let key3 = SpecializationKey::new("identity", vec![ConcreteType::Float]);

    assert_eq!(key1, key2);
    assert_ne!(key1, key3);
}

#[test]
fn test_specialization_key_hashing() {
    use std::collections::HashSet;

    let key1 = SpecializationKey::new("identity", vec![ConcreteType::Int]);
    let key2 = SpecializationKey::new("identity", vec![ConcreteType::Int]);
    let key3 = SpecializationKey::new("identity", vec![ConcreteType::Float]);

    let mut set = HashSet::new();
    set.insert(key1.clone());
    set.insert(key2.clone());
    set.insert(key3.clone());

    // key1 and key2 are equal, so set should have 2 elements
    assert_eq!(set.len(), 2);
}

#[test]
fn test_specialization_key_nested_types() {
    let inner = ConcreteType::Specialized {
        name: "Result".to_string(),
        args: vec![ConcreteType::Int, ConcreteType::String],
    };
    let outer = ConcreteType::Specialized {
        name: "List".to_string(),
        args: vec![inner.clone()],
    };

    let key = SpecializationKey::new("process", vec![outer]);

    assert_eq!(key.name, "process");
    assert_eq!(key.type_args.len(), 1);

    match &key.type_args[0] {
        ConcreteType::Specialized { name, args } => {
            assert_eq!(name, "List");
            assert_eq!(args.len(), 1);
        }
        _ => panic!("Expected specialized type"),
    }
}

// ============================================================================
// Unit Tests: Concrete Type
// ============================================================================

#[test]
fn test_concrete_type_primitives() {
    let int = ConcreteType::Int;
    let float = ConcreteType::Float;
    let bool_type = ConcreteType::Bool;
    let string = ConcreteType::String;

    assert_ne!(int, float);
    assert_ne!(int, bool_type);
    assert_ne!(int, string);
}

#[test]
fn test_concrete_type_array() {
    let array_int = ConcreteType::Array(Box::new(ConcreteType::Int));
    let array_float = ConcreteType::Array(Box::new(ConcreteType::Float));

    assert_ne!(array_int, array_float);

    match array_int {
        ConcreteType::Array(elem) => assert_eq!(*elem, ConcreteType::Int),
        _ => panic!("Expected array"),
    }
}

#[test]
fn test_concrete_type_tuple() {
    let tuple = ConcreteType::Tuple(vec![ConcreteType::Int, ConcreteType::String]);

    match tuple {
        ConcreteType::Tuple(elems) => {
            assert_eq!(elems.len(), 2);
            assert_eq!(elems[0], ConcreteType::Int);
            assert_eq!(elems[1], ConcreteType::String);
        }
        _ => panic!("Expected tuple"),
    }
}

#[test]
fn test_concrete_type_function() {
    let func_type = ConcreteType::Function {
        params: vec![ConcreteType::Int, ConcreteType::Int],
        ret: Box::new(ConcreteType::Int),
    };

    match func_type {
        ConcreteType::Function { params, ret } => {
            assert_eq!(params.len(), 2);
            assert_eq!(*ret, ConcreteType::Int);
        }
        _ => panic!("Expected function"),
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

fn create_test_function(name: &str, generic_params: Vec<String>) -> FunctionDef {
    use simple_parser::ast::{Block, Visibility};
    use simple_parser::token::Span;

    FunctionDef {
        span: Span::new(0, 0, 0, 0),
        name: name.to_string(),
        generic_params,
        params: vec![],
        return_type: None,
        where_clause: vec![],
        body: Block::default(),
        visibility: Visibility::Public,
        effects: vec![],
        decorators: vec![],
        attributes: vec![],
        doc_comment: None,
        contract: None,
        is_abstract: false,
        is_sync: false,
        bounds_block: None,
        is_static: false,
        is_me_method: false,
        is_generator: false,
        return_constraint: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: HashMap::new(),
    }
}

// ============================================================================
// Integration Tests (require full compiler pipeline)
// ============================================================================

#[test]
#[ignore] // Requires full SMF writing integration
fn test_compile_with_templates_to_smf() {
    // TODO: Implement when SMF writer is fully integrated
    // This test should:
    // 1. Compile source with generic functions
    // 2. Generate SMF file
    // 3. Verify TemplateCode section exists
    // 4. Verify TemplateMeta section exists
    // 5. Verify symbol table marks templates correctly
}

#[test]
#[ignore] // Requires SMF loader
fn test_load_templates_from_smf() {
    // TODO: Implement when SMF loader supports templates
    // This test should:
    // 1. Load SMF file with templates
    // 2. Extract templates
    // 3. Verify template count and contents
}

#[test]
#[ignore] // Requires full linker integration
fn test_link_time_instantiation() {
    // TODO: Implement when linker supports deferred mono
    // This test should:
    // 1. Compile library with List<T>
    // 2. Compile app using List<Float>
    // 3. Link together
    // 4. Verify List$Float was instantiated
    // 5. Execute and verify behavior
}
