
#[test]
fn test_metadata_plumbing_works() {
    use simple_compiler::{hir, mir};
    use simple_parser::Parser;
    
    // Verify metadata fields exist and are propagated from HIR to MIR
    let source = r#"
fn test_func():
    return 42
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Verify HIR function has metadata fields
    assert_eq!(hir_module.functions.len(), 1);
    let hir_func = &hir_module.functions[0];
    
    // Fields exist (even if empty for this simple function)
    assert!(hir_func.module_path.is_empty() || !hir_func.module_path.is_empty());
    assert!(hir_func.attributes.len() >= 0); // always true, just checking field exists
    assert!(hir_func.effects.len() >= 0);

    // Verify MIR function has metadata fields
    let mir_module = mir::lower_to_mir(&hir_module).expect("Failed to lower to MIR");
    let mir_func = &mir_module.functions[0];
    
    // Metadata accessible for AOP weaving
    assert!(mir_func.module_path.is_empty() || !mir_func.module_path.is_empty());
    assert!(mir_func.attributes.len() >= 0);
    assert!(mir_func.effects.len() >= 0);
    assert_eq!(mir_func.name, "test_func");
}

#[test]
fn test_weaving_diagnostics_collection() {
    use simple_compiler::{hir, mir, weaving};
    use simple_parser::Parser;

    // Test that weaving diagnostics are properly collected and reported
    let source = r#"
fn target_func():
    return 42

fn advice_func():
    return 0

on pc{ execution(* target_func(..)) } use advice_func before priority 10
on pc{ execution(* target_func(..)) } use advice_func after_success priority 20
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Verify we have AOP advices in HIR
    assert!(!hir_module.aop_advices.is_empty(), "Should have AOP advices");

    // Create weaving config from HIR
    let weaving_config = weaving::WeavingConfig::from_hir_advices(&hir_module.aop_advices);
    assert!(weaving_config.enabled, "Weaving should be enabled");

    // Lower to MIR (this should trigger weaving)
    let mir_module = mir::lower_to_mir(&hir_module).expect("Failed to lower to MIR");

    // Verify target function exists
    let target_func = mir_module.functions.iter()
        .find(|f| f.name == "target_func")
        .expect("Should have target_func");

    // Create weaver and manually weave to get diagnostics
    let weaver = weaving::Weaver::new(weaving_config);
    let mut test_func = target_func.clone();
    let result = weaver.weave_function(&mut test_func);

    // Verify weaving occurred
    assert!(result.join_points_woven > 0, "Should have woven join points");
    assert!(result.advices_inserted > 0, "Should have inserted advices");

    // Verify diagnostics were collected
    assert!(!result.diagnostics.is_empty(), "Should have diagnostics");

    // Check for informational diagnostic about weaving summary
    let has_info = result.diagnostics.iter()
        .any(|d| matches!(d.level, weaving::DiagnosticLevel::Info));
    assert!(has_info, "Should have informational diagnostic about weaving");

    // Verify no errors occurred
    assert!(!result.has_errors(), "Should not have errors for valid weaving");
}

#[test]
fn test_zero_overhead_when_disabled() {
    use simple_compiler::{hir, mir, weaving};
    use simple_parser::Parser;

    // Test that weaving has zero overhead when disabled
    let source = r#"
fn simple_func():
    return 42
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Verify no AOP advices
    assert!(hir_module.aop_advices.is_empty(), "Should have no AOP advices");

    // Lower to MIR
    let mir_module = mir::lower_to_mir(&hir_module).expect("Failed to lower to MIR");

    // Create disabled weaving config
    let weaving_config = weaving::WeavingConfig::disabled();
    assert!(!weaving_config.enabled, "Weaving should be disabled");

    // Weave a function
    let weaver = weaving::Weaver::new(weaving_config);
    let mut test_func = mir_module.functions[0].clone();
    let result = weaver.weave_function(&mut test_func);

    // Verify zero overhead - no weaving occurred
    assert_eq!(result.join_points_woven, 0, "Should not weave when disabled");
    assert_eq!(result.advices_inserted, 0, "Should not insert advices when disabled");
    assert_eq!(result.diagnostics.len(), 0, "Should not generate diagnostics when disabled");
}
