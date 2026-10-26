//! Imported SPipe functions must retain their owner and callback contract.
use simple_compiler::hir::{HirExpr, HirExprKind, HirModule, HirStmt, Lowerer};
use simple_compiler::module_resolver::ModuleResolver;
use simple_parser::Parser;
use std::fs;

const OWNER: &str = "struct Check:\n    value: i64\n    fn to_equal(self, expected: i64) -> bool:\n        self.value == expected\nfn expect(value: i64) -> Check:\n    Check(value: value)\nfn it(name: text, body: fn()):\n    body()\nfn describe(name: text, body: fn()):\n    body()\nfn before_each(body: fn()):\n    body()\nfn after_each(body: fn()):\n    body()\nfn helper() -> i64:\n    17\n";

fn lower_fixture(source: &str) -> HirModule {
    let dir = tempfile::tempdir().unwrap();
    let src = dir.path().join("src");
    fs::create_dir_all(src.join("owner")).unwrap();
    fs::write(src.join("owner/bdd.spl"), OWNER).unwrap();
    fs::write(src.join("owner/facade.spl"), "export use owner.bdd.{it, describe, expect}\n").unwrap();
    let entry = src.join("main.spl");
    fs::write(&entry, source).unwrap();
    let ast = Parser::new(source).parse().expect("real fixture parses");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
    let mut lowerer = Lowerer::with_module_resolver(resolver, entry);
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    lowerer.lower_module(&ast).expect("real fixture lowers")
}

fn statement<'a>(module: &'a HirModule, name: &str) -> &'a HirExpr {
    let function = module.functions.iter().find(|f| f.name == name).expect(name);
    function.body.iter().find_map(|stmt| match stmt {
        HirStmt::Expr(expr) => Some(expr),
        _ => None,
    }).expect("observable call statement")
}

fn assert_ordinary_call(module: &HirModule, function: &str, arg_count: usize) {
    let expression = statement(module, function);
    let HirExprKind::Call { args, .. } = &expression.kind else {
        panic!("resolved callable must remain a call: {expression:?}");
    };
    assert_eq!(args.len(), arg_count, "callback arguments are preserved");
    let lowered = format!("{:?}", module.functions.iter().find(|f| f.name == function).unwrap().body);
    assert!(!lowered.contains("rt_bdd_"), "imported owner was bypassed: {lowered}");
}

#[test]
fn native_bdd_imported_named_callbacks_keep_registry_owner() {
    let module = lower_fixture("use owner.bdd.{it, describe}\nfn body():\n    print \"callback body\"\nfn register_case():\n    it(\"case\", body)\n    0\nfn register_suite():\n    describe(\"suite\", body)\n    0\n");
    assert_ordinary_call(&module, "register_case", 2);
    assert_ordinary_call(&module, "register_suite", 2);
}

#[test]
fn native_bdd_imported_matcher_keeps_expectation_owner() {
    let module = lower_fixture("use owner.bdd.{expect}\nfn verify():\n    expect(42).to_equal(43)\n    0\n");
    let expression = statement(&module, "verify");
    let debug = format!("{expression:?}");
    assert!(!debug.contains("rt_bdd_"), "imported matcher bypassed owner: {debug}");
    assert!(debug.contains("to_equal") && debug.contains("expect"), "both real callable owners must survive: {debug}");
}

#[test]
fn native_bdd_local_callable_shadows_intrinsic() {
    let module = lower_fixture("fn it(name: text, body: fn()):\n    body()\nfn body():\n    print \"callback body\"\nfn register_case():\n    it(\"case\", body)\n    0\n");
    assert_ordinary_call(&module, "register_case", 2);
}

#[test]
fn native_bdd_lexical_callback_parameter_shadows_intrinsic() {
    let module = lower_fixture("fn invoke(it: fn()):\n    it()\n    0\n");
    assert_ordinary_call(&module, "invoke", 0);
}

#[test]
fn native_bdd_alias_and_reexport_keep_callable() {
    for import in ["use owner.bdd.{it as selected}", "use owner.facade.{it as selected}"] {
        let module = lower_fixture(&format!("{import}\nfn body():\n    print \"callback body\"\nfn register_case():\n    selected(\"case\", body)\n    0\n"));
        assert_ordinary_call(&module, "register_case", 2);
    }
}

#[test]
fn native_bdd_qualified_call_keeps_callable() {
    let module = lower_fixture("use owner.bdd\nfn body():\n    print \"callback body\"\nfn register_case():\n    bdd.it(\"case\", body)\n    0\n");
    let expression = statement(&module, "register_case");
    let debug = format!("{expression:?}");
    assert!(!debug.contains("rt_bdd_"), "qualified callable intercepted: {debug}");
    assert!(debug.contains("body"), "callback value was discarded: {debug}");
}

#[test]
fn native_bdd_unbound_dsl_preserves_real_body_and_failure() {
    let module = lower_fixture("fn legacy():\n    it \"case\":\n        expect(false)\n    0\n");
    let function = module.functions.iter().find(|f| f.name == "legacy").unwrap();
    let debug = format!("{:?}", function.body);
    assert!(debug.contains("rt_bdd_it_start_rv"), "missing start: {debug}");
    assert!(debug.contains("rt_bdd_expect_truthy_rv"), "assertion body lost: {debug}");
    assert!(debug.contains("rt_bdd_it_end"), "missing end: {debug}");
}

#[test]
fn native_bdd_unrelated_same_name_does_not_disable_intrinsic() {
    let module = lower_fixture("use owner.bdd.{helper}\nfn legacy():\n    it \"case\":\n        expect(false)\n    0\n");
    let function = module.functions.iter().find(|f| f.name == "legacy").unwrap();
    let debug = format!("{:?}", function.body);
    assert!(debug.contains("rt_bdd_it_start_rv"), "unimported owner's it must not capture DSL: {debug}");
    assert!(debug.contains("rt_bdd_expect_truthy_rv"), "unimported owner's expect must not capture DSL: {debug}");
}

#[test]
fn native_bdd_imported_hooks_keep_registration_and_order() {
    let module = lower_fixture("use owner.bdd.{before_each, after_each}\nfn body():\n    print \"hook callback\"\nfn register_hooks():\n    before_each(body)\n    after_each(body)\n    0\n");
    let function = module.functions.iter().find(|f| f.name == "register_hooks").unwrap();
    let calls: Vec<_> = function.body.iter().filter_map(|stmt| match stmt {
        HirStmt::Expr(HirExpr { kind: HirExprKind::Call { func, args }, .. }) => Some((func, args)),
        _ => None,
    }).collect();
    assert_eq!(calls.len(), 2, "both hook registrations must survive: {:?}", function.body);
    assert!(format!("{:?}", calls[0].0).contains("before_each"));
    assert!(format!("{:?}", calls[1].0).contains("after_each"));
    assert!(calls.iter().all(|(_, args)| args.len() == 1));
}

#[test]
fn native_bdd_imported_colon_block_keeps_registry_owner() {
    let module = lower_fixture("use owner.bdd.{it}\nfn register_case():\n    it \"case\":\n        print \"real callback\"\n    0\n");
    assert_ordinary_call(&module, "register_case", 2);
}
