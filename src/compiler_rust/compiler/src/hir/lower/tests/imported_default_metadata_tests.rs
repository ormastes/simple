use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{HirExprKind, HirStmt, TypeId};
use crate::module_resolver::ModuleResolver;
use crate::test_helpers::create_test_project;
use simple_parser::Parser;
use std::fs;

#[test]
fn coverage_metadata_imported_defaults_and_aliases_keep_literals() {
    let dir = create_test_project();
    let src = dir.path().join("src");
    fs::create_dir_all(src.join("owner")).unwrap();
    fs::write(src.join("owner/defaults.spl"),
        "fn filters(enabled: bool, include: text = \"\", exclude: text = \"blocked\") -> text:\n    include + exclude\n").unwrap();
    fs::write(src.join("owner/shim.spl"), "export use owner.defaults.{filters}\n").unwrap();
    fs::write(src.join("owner/renamed.spl"), "export use owner.defaults.{filters as exposed_filters}\n").unwrap();
    for (import, called, local) in [
        ("use owner.defaults.{filters}", "filters", ""),
        ("use owner.defaults.{filters as imported_filters}", "imported_filters", "fn filters(enabled: bool, include: text = \"local\", exclude: text = \"only\") -> text:\n    include + exclude\n"),
        ("use owner.shim.{filters}", "filters", ""),
        ("use owner.shim.{filters as imported_filters}", "imported_filters", "fn filters(enabled: bool, include: text = \"local\", exclude: text = \"only\") -> text:\n    include + exclude\n"),
        ("use owner.renamed.{exposed_filters as imported_filters}", "imported_filters", "fn filters(enabled: bool, include: text = \"local\", exclude: text = \"only\") -> text:\n    include + exclude\nfn exposed_filters(enabled: bool, include: text = \"local\", exclude: text = \"only\") -> text:\n    include + exclude\n"),
    ] {
        let mut source = format!("{import}\n{local}\nfn omitted() -> text:\n    {called}(true)\nfn partial() -> text:\n    {called}(false, \"supplied\")\nfn explicit() -> text:\n    {called}(true, \"a\", \"b\")\n");
        let mut cases = vec![("omitted", ["", "blocked"]), ("partial", ["supplied", "blocked"]), ("explicit", ["a", "b"])];
        if !local.is_empty() {
            source.push_str("fn local_call() -> text:\n    filters(true)\n");
            cases.push(("local_call", ["local", "only"]));
        }
        let ast = Parser::new(&source).parse().expect("parse defaults fixture");
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
        let lowerer = Lowerer::with_module_resolver(resolver, src.join("main.spl"));
        let module = lowerer.lower_module(&ast).expect("lower imported defaults");
        for (name, expected) in cases {
            let function = module.functions.iter().find(|f| f.name == name).unwrap();
            let call = function.body.iter().find_map(|stmt| match stmt {
                HirStmt::Expr(expr) | HirStmt::Return(Some(expr)) => Some(expr),
                _ => None,
            }).unwrap();
            let HirExprKind::Call { args, .. } = &call.kind else { panic!("expected call: {call:?}") };
            assert_eq!(args.len(), 3, "{import}: {name}");
            for (arg, text) in args[1..].iter().zip(expected) {
                assert_eq!(arg.ty, TypeId::STRING);
                assert!(matches!(&arg.kind, HirExprKind::String(value) if value == text), "{import}: {name}: {arg:?}");
            }
        }
    }
}

fn call_args<'a>(module: &'a crate::hir::HirModule, name: &str) -> &'a [crate::hir::HirExpr] {
    let function = module.functions.iter().find(|f| f.name == name).expect(name);
    let expr = function.body.iter().find_map(|stmt| match stmt {
        HirStmt::Expr(expr) | HirStmt::Return(Some(expr)) => Some(expr),
        _ => None,
    }).expect("call statement");
    let HirExprKind::Call { args, .. } = &expr.kind else { panic!("expected call: {expr:?}"); };
    args
}

#[test]
fn imported_defaults_literal_fstring_is_constant_but_interpolation_is_not() {
    let source = "fn fixed(x: text = \"plain\") -> text:\n    x\nfn dynamic(x: text = \"{caller}\") -> text:\n    x\nfn literal_call() -> text:\n    fixed()\nfn dynamic_call(caller: text) -> text:\n    dynamic()\n";
    let ast = Parser::new(source).parse().unwrap();
    let simple_parser::Node::Function(fixed) = &ast.items[0] else { panic!("function"); };
    assert!(matches!(&fixed.params[0].default,
        Some(simple_parser::Expr::FString { parts, .. })
        if parts.iter().all(|part| matches!(part, simple_parser::ast::FStringPart::Literal(_)))));
    // An interpolated default must never be lowered in the caller (it would
    // capture caller locals); omitting it is a compile error, never an
    // unfilled slot that native codegen pads with tagged nil.
    let err = crate::hir::lower(&ast).expect_err("non-constant omitted default must not lower");
    assert!(format!("{err}").contains("`dynamic` omits argument 1"), "{err}");
    let literal_only = Parser::new("fn fixed(x: text = \"plain\") -> text:\n    x\nfn literal_call() -> text:\n    fixed()\n").parse().unwrap();
    let module = crate::hir::lower(&literal_only).unwrap();
    let args = call_args(&module, "literal_call");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].kind, HirExprKind::String(s) if s == "plain"));
}

#[test]
fn imported_defaults_cached_facade_keeps_owner_identity() {
    let dir = create_test_project();
    let src = dir.path().join("src");
    fs::write(src.join("a.spl"), "fn f(x: text = \"owner-a\") -> text:\n    x\n").unwrap();
    fs::write(src.join("b.spl"), "fn f(x: text = \"owner-b\") -> text:\n    x\n").unwrap();
    fs::write(src.join("facade.spl"), "export use a.{f}\n").unwrap();
    let source = "use a.{f}\nuse b.{f as b_f}\nuse facade.{f as via}\nfn from_a() -> text:\n    f()\nfn from_b() -> text:\n    b_f()\nfn from_facade() -> text:\n    via()\n";
    let ast = Parser::new(source).parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let module = Lowerer::with_module_resolver(resolver, src.join("main.spl")).lower_module(&ast).unwrap();
    for (name, expected) in [("from_a", "owner-a"), ("from_b", "owner-b"), ("from_facade", "owner-a")] {
        let args = call_args(&module, name);
        assert_eq!(args.len(), 1, "{name}");
        assert!(matches!(&args[0].kind, HirExprKind::String(s) if s == expected), "{name}: {args:?}");
    }
}

#[test]
fn imported_defaults_alias_in_consumer_does_not_overwrite_source_declaration() {
    let dir = create_test_project();
    let src = dir.path().join("src");
    fs::write(src.join("a.spl"), "fn f(x: text = \"F\") -> text:\n    x\nfn g(x: text = \"G\") -> text:\n    x\n").unwrap();
    fs::write(src.join("consumer.spl"), "use a.{f as g}\nfn h() -> text:\n    g()\n").unwrap();
    fs::write(src.join("facade.spl"), "export use a.{g}\n").unwrap();
    let source = "use a.{g}\nuse consumer.{h}\nuse facade.{g as via}\nfn probe() -> text:\n    via()\n";
    let ast = Parser::new(source).parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let module = Lowerer::with_module_resolver(resolver, src.join("main.spl")).lower_module(&ast).unwrap();
    let args = call_args(&module, "probe");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].kind, HirExprKind::String(s) if s == "G"));
}

#[test]
fn imported_defaults_required_local_parameter_does_not_acquire_import_default() {
    let dir = create_test_project();
    let src = dir.path().join("src");
    fs::write(src.join("owner.spl"), "fn f(x: text = \"imported\") -> text:\n    x\n").unwrap();
    let source = "use owner.{f as imported_f}\nfn f(x: text) -> text:\n    x\nfn probe() -> text:\n    f()\nfn imported_probe() -> text:\n    imported_f()\n";
    let ast = Parser::new(source).parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let module = Lowerer::with_module_resolver(resolver, src.join("main.spl")).lower_module(&ast).unwrap();
    assert!(call_args(&module, "probe").is_empty());
    let args = call_args(&module, "imported_probe");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].kind, HirExprKind::String(s) if s == "imported"));
}

#[test]
fn imported_defaults_do_not_attach_to_local_callable_or_named_call() {
    let dir = create_test_project();
    let src = dir.path().join("src");
    fs::write(src.join("owner.spl"), "fn f(x: bool, extra: text = \"owner\") -> text:\n    extra\n").unwrap();
    let source = "use owner.{f}\nfn local_call(f: fn(bool) -> text) -> text:\n    f(true)\nfn named_call() -> text:\n    f(x: true)\n";
    let ast = Parser::new(source).parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let module = Lowerer::with_module_resolver(resolver, src.join("main.spl")).lower_module(&ast).unwrap();
    assert_eq!(call_args(&module, "local_call").len(), 1);
    assert_eq!(call_args(&module, "named_call").len(), 1);
}

#[test]
fn imported_defaults_flattened_functions_use_resolved_owner_symbol() {
    let mut ast = Parser::new("fn f(x: text = \"owner-a\") -> text:\n    x\nfn call_a() -> text:\n    f()\nfn f(x: text = \"owner-b\") -> text:\n    x\nfn call_b() -> text:\n    f()\n").parse().unwrap();
    for (index, node) in ast.items.iter_mut().enumerate() {
        if let simple_parser::Node::Function(function) = node {
            crate::interpreter::tag_function_module_owner(function, if index < 2 { "owner-a" } else { "owner-b" });
        }
    }
    let module = crate::hir::lower(&ast).unwrap();
    for (name, expected) in [("call_a", "owner-a"), ("call_b", "owner-b")] {
        let args = call_args(&module, name);
        assert_eq!(args.len(), 1, "{name}");
        assert!(matches!(&args[0].kind, HirExprKind::String(s) if s == expected), "{name}: {args:?}");
    }
}

fn method_call_args<'a>(module: &'a crate::hir::HirModule, name: &str) -> &'a [crate::hir::HirExpr] {
    let function = module.functions.iter().find(|f| f.name == name).expect(name);
    let expr = function.body.iter().find_map(|stmt| match stmt {
        HirStmt::Expr(expr) | HirStmt::Return(Some(expr)) => Some(expr),
        _ => None,
    }).expect("call statement");
    let HirExprKind::MethodCall { args, .. } = &expr.kind else { panic!("expected method call: {expr:?}"); };
    args
}

#[test]
fn imported_method_defaults_fill_cross_module_method_calls() {
    // A method with a defaulted parameter declared in ANOTHER module (on the
    // class body and in a separate impl block) must have its omitted trailing
    // argument filled at the call site. Before, only same-module methods were
    // filled and the callee read an unset argument slot on the native lane.
    let dir = create_test_project();
    let src = dir.path().join("src");
    fs::write(src.join("owner.spl"),
        "class Table:\n    var n: i64\n\n    fn body(x: i64, flag: bool = true) -> bool:\n        flag\n\nimpl Table:\n    fn split(x: i64, tag: text = \"dflt\") -> text:\n        tag\n").unwrap();
    Parser::new(&fs::read_to_string(src.join("owner.spl")).unwrap()).parse().expect("owner parses");
    let source = "use owner.{Table}\nfn from_class() -> bool:\n    Table(n: 1).body(1)\nfn from_impl() -> text:\n    Table(n: 1).split(1)\nfn explicit() -> bool:\n    Table(n: 1).body(1, false)\n";
    let ast = Parser::new(source).parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let module = Lowerer::with_module_resolver(resolver, src.join("main.spl")).lower_module(&ast).unwrap();
    let body = method_call_args(&module, "from_class");
    assert_eq!(body.len(), 2, "{body:?}");
    assert!(matches!(&body[1].kind, HirExprKind::Bool(true)), "{body:?}");
    let split = method_call_args(&module, "from_impl");
    assert_eq!(split.len(), 2, "{split:?}");
    assert!(matches!(&split[1].kind, HirExprKind::String(s) if s == "dflt"), "{split:?}");
    let explicit = method_call_args(&module, "explicit");
    assert_eq!(explicit.len(), 2);
    assert!(matches!(&explicit[1].kind, HirExprKind::Bool(false)));
}

/// Cross-module omitted defaults of container / typed-literal shape are filled
/// at the call site for free functions AND imported class methods; a default
/// that cannot be materialised there is a compile error. Regression for the
/// stage3 `MirLowering.lower_module(hir, [], false)` SIGSEGV, whose omitted
/// `archive_trait_thunks: [MirFunction] = []` was padded with tagged nil.
#[test]
fn imported_container_and_typed_defaults_fill_and_non_constant_default_errors() {
    let dir = create_test_project();
    let src = dir.path().join("src");
    fs::write(src.join("owner.spl"), concat!(
        "class Lowering:\n    base: i64\n",
        "    me lower(x: i64, providers: [i64] = [], is_entry: bool = true, syms: [i64]? = nil, thunks: [i64] = [], k: i64 = 7) -> i64:\n        x\n",
        "fn fold(x: i64, items: [i64] = [], k: i64 = 7, flag: bool = true, limit: u64 = 16u64, seen: {text: bool} = {}, pair: (i64, i64) = (1, 2)) -> i64:\n    x\n",
        "val LIMIT = 3\n",
        "fn needs_global(x: i64, limit: i64 = LIMIT) -> i64:\n    x\n",
    )).unwrap();
    let source = "use owner.{Lowering, fold}\nfn free_call() -> i64:\n    fold(1)\nfn method_call(low: Lowering) -> i64:\n    low.lower(2, [], false)\n";
    let ast = Parser::new(source).parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let module = Lowerer::with_module_resolver(resolver, src.join("main.spl")).lower_module(&ast).unwrap();
    let args = call_args(&module, "free_call");
    assert_eq!(args.len(), 7, "{args:?}");
    assert!(matches!(&args[1].kind, HirExprKind::Array(items) if items.is_empty()), "{:?}", args[1]);
    assert!(matches!(&args[2].kind, HirExprKind::Integer(7)), "{:?}", args[2]);
    assert!(matches!(&args[3].kind, HirExprKind::Bool(true)), "{:?}", args[3]);

    let function = module.functions.iter().find(|f| f.name == "method_call").unwrap();
    let call = function.body.iter().find_map(|stmt| match stmt {
        HirStmt::Expr(expr) | HirStmt::Return(Some(expr)) => Some(expr),
        _ => None,
    }).unwrap();
    let HirExprKind::MethodCall { args, .. } = &call.kind else { panic!("expected method call: {call:?}") };
    assert_eq!(args.len(), 6, "receiver excluded; every omitted default filled: {args:?}");
    assert!(matches!(&args[3].kind, HirExprKind::Nil), "{:?}", args[3]);
    assert!(matches!(&args[4].kind, HirExprKind::Array(items) if items.is_empty()), "{:?}", args[4]);
    assert!(matches!(&args[5].kind, HirExprKind::Integer(7)), "{:?}", args[5]);

    let bad = Parser::new("use owner.{needs_global}\nfn probe() -> i64:\n    needs_global(1)\n").parse().unwrap();
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let err = Lowerer::with_module_resolver(resolver, src.join("main.spl")).lower_module(&bad)
        .expect_err("callee-module global default cannot be materialised in the caller");
    assert!(format!("{err}").contains("`needs_global` omits argument 2"), "{err}");
}
