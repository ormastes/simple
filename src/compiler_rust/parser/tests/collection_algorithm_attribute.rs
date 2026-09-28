use simple_parser::ast::{Expr, Node};
use simple_parser::Parser;

fn parse(source: &str) -> simple_parser::ast::Module {
    Parser::new(source)
        .with_collection_module_path("app/collection_probe.spl")
        .parse()
        .expect("collection source parses")
}

fn assert_wrapped<'a>(value: &'a Expr, family: &str, algorithm: &str) -> &'a str {
    let Expr::MethodCall { receiver, method, args, .. } = value else {
        panic!("expected collection attribute wrapper: {value:?}");
    };
    assert_eq!(receiver.as_ref(), &Expr::Identifier(family.to_string()));
    assert_eq!(method, "attributed_at_site");
    assert_eq!(args.len(), 3);
    assert_eq!(args[1].value, Expr::String(algorithm.to_string()));
    let Expr::String(site) = &args[2].value else { panic!("expected site ID") };
    site
}

#[test]
fn local_attributes_wrap_only_their_own_container() {
    let module = parse(
        "fn main():\n    @collection_algorithm(\"hash\")\n    var hot = AdaptiveTextSet.new()\n    @collection_algorithm(\"linear\")\n    val cold = AdaptiveTextMap.new()\n",
    );
    let Node::Function(function) = &module.items[0] else { panic!("expected function") };
    let Node::Let(hot) = &function.body.statements[0] else { panic!("expected hot binding") };
    let Node::Let(cold) = &function.body.statements[1] else { panic!("expected cold binding") };
    let hot_site = assert_wrapped(hot.value.as_ref().unwrap(), "AdaptiveTextSet", "hash");
    let cold_site = assert_wrapped(cold.value.as_ref().unwrap(), "AdaptiveTextMap", "linear");
    assert!(hot_site.starts_with("ast://app/collection_probe.spl/main/local/hot#"));
    assert!(cold_site.starts_with("ast://app/collection_probe.spl/main/local/cold#"));
    assert_ne!(hot_site, cold_site);
}

#[test]
fn field_attribute_wraps_initialized_field() {
    let module = parse(
        "class Store:\n    @collection_algorithm(\"ordered\")\n    values: AdaptiveTextSet = AdaptiveTextSet.new()\n",
    );
    let Node::Class(class) = &module.items[0] else { panic!("expected class") };
    let site = assert_wrapped(class.fields[0].default.as_ref().unwrap(), "AdaptiveTextSet", "ordered");
    assert_eq!(site, "ast://app/collection_probe.spl/Store/values#-555445139409988573");
}

#[test]
fn typed_factory_initializers_keep_their_declared_collection_family() {
    let module = parse(
        "fn main():\n    @collection_algorithm(\"hash\")\n    var hot: AdaptiveTextSet = make_set()\n    @collection_algorithm(\"ordered\")\n    val generic: AdaptiveMap<i64, text> = make_map()\n",
    );
    let Node::Function(function) = &module.items[0] else { panic!("expected function") };
    let Node::Let(hot) = &function.body.statements[0] else { panic!("expected hot binding") };
    let Node::Let(generic) = &function.body.statements[1] else { panic!("expected generic binding") };
    assert_wrapped(hot.value.as_ref().unwrap(), "AdaptiveTextSet", "hash");
    assert_wrapped(generic.value.as_ref().unwrap(), "AdaptiveMap", "ordered");

    let field_module = parse(
        "class Store:\n    @collection_algorithm(\"ordered\")\n    values: AdaptiveTextMap = make_map()\n",
    );
    let Node::Class(class) = &field_module.items[0] else { panic!("expected class") };
    assert_wrapped(class.fields[0].default.as_ref().unwrap(), "AdaptiveTextMap", "ordered");
}

#[test]
fn named_nested_functions_own_their_collection_sites() {
    let module = parse(
        "fn outer():\n    fn left():\n        @collection_algorithm(\"auto\")\n        val chosen = AdaptiveTextSet.new()\n    fn right():\n        @collection_algorithm(\"auto\")\n        val chosen = AdaptiveTextSet.new()\n",
    );
    let Node::Function(outer) = &module.items[0] else { panic!("expected outer function") };
    let Node::Function(left) = &outer.body.statements[0] else { panic!("expected left function") };
    let Node::Function(right) = &outer.body.statements[1] else { panic!("expected right function") };
    let Node::Let(left_binding) = &left.body.statements[0] else { panic!("expected left binding") };
    let Node::Let(right_binding) = &right.body.statements[0] else { panic!("expected right binding") };
    let left_site = assert_wrapped(left_binding.value.as_ref().unwrap(), "AdaptiveTextSet", "auto");
    let right_site = assert_wrapped(right_binding.value.as_ref().unwrap(), "AdaptiveTextSet", "auto");
    assert!(left_site.contains("/outer/left/local/chosen#"));
    assert!(right_site.contains("/outer/right/local/chosen#"));
    assert_ne!(left_site, right_site);
}

#[test]
fn explicit_literal_site_is_the_wrapped_profile_site() {
    let module = parse(
        "fn main():\n    @collection_algorithm(\"auto\")\n    var hot = AdaptiveTextSet.with_site_and_target(policy, \"ast://module/manual#stable\", \"x86_64-v3\")\n",
    );
    let Node::Function(function) = &module.items[0] else { panic!("expected function") };
    let Node::Let(binding) = &function.body.statements[0] else { panic!("expected binding") };
    assert_eq!(
        assert_wrapped(binding.value.as_ref().unwrap(), "AdaptiveTextSet", "auto"),
        "ast://module/manual#stable"
    );
}

#[test]
fn site_identity_survives_algorithm_switch_and_unrelated_line_insertion() {
    fn site(source: &str) -> String {
        let module = parse(source);
        let Node::Function(function) = &module.items[0] else { panic!("expected function") };
        let Node::Let(binding) = &function.body.statements[0] else { panic!("expected binding") };
        assert_wrapped(binding.value.as_ref().unwrap(), "AdaptiveTextSet", "auto").to_string()
    }
    let first = site("fn main():\n    @collection_algorithm(\"auto\")\n    var hot = AdaptiveTextSet.new()\n");
    // Canonical rt_hash_text/FNV-1a over the declaration without its attribute.
    assert_eq!(first, "ast://app/collection_probe.spl/main/local/hot#-7095170762293803234");
    let shifted = site("fn main():\n    # unrelated line\n    @collection_algorithm(\"auto\")\n    var hot = AdaptiveTextSet.new()\n");
    assert_eq!(first, shifted);

    let module = parse("fn main():\n    @collection_algorithm(\"hash\")\n    var hot = AdaptiveTextSet.new()\n");
    let Node::Function(function) = &module.items[0] else { panic!("expected function") };
    let Node::Let(binding) = &function.body.statements[0] else { panic!("expected binding") };
    let switched = assert_wrapped(binding.value.as_ref().unwrap(), "AdaptiveTextSet", "hash");
    assert_eq!(first, switched);
}

#[test]
fn absolute_source_path_uses_the_same_project_relative_site() {
    let source = "fn main():\n    @collection_algorithm(\"auto\")\n    var hot = AdaptiveTextSet.new()\n";
    let path = std::env::current_dir().unwrap().join("app/collection_probe.spl");
    let module = Parser::new(source)
        .with_collection_module_path(path.to_str().unwrap())
        .parse()
        .expect("absolute-path collection source parses");
    let Node::Function(function) = &module.items[0] else { panic!("expected function") };
    let Node::Let(binding) = &function.body.statements[0] else { panic!("expected binding") };
    let site = assert_wrapped(binding.value.as_ref().unwrap(), "AdaptiveTextSet", "auto");
    assert_eq!(site, "ast://app/collection_probe.spl/main/local/hot#-7095170762293803234");
}

#[test]
fn differential_semantics_fixture_parses_with_six_attributed_sites() {
    for (source, set_family, map_family, expected_bindings) in [
        (include_str!("../../../../test/fixtures/profile_switchable/semantics_probe.spl"), "AdaptiveTextSet", "AdaptiveTextMap", 6),
        (include_str!("../../../../test/fixtures/profile_switchable/generic_semantics_probe.spl"), "AdaptiveSet", "AdaptiveMap", 8),
    ] {
        let module = parse(source);
        let main = module.items.iter().find_map(|item| match item {
            Node::Function(function) if function.name == "main" => Some(function),
            _ => None,
        }).expect("semantics fixture has main");
        let attributed = main.body.statements.iter()
            .filter(|statement| matches!(statement, Node::Let(_))).count();
        assert_eq!(attributed, expected_bindings);
        let expected = [
            (set_family, "linear"), (set_family, "hash"), (set_family, "ordered"),
            (map_family, "linear"), (map_family, "hash"), (map_family, "ordered"),
        ];
        for (statement, (family, algorithm)) in main.body.statements.iter().take(6).zip(expected) {
            let Node::Let(binding) = statement else { panic!("expected attributed binding") };
            assert_wrapped(binding.value.as_ref().unwrap(), family, algorithm);
        }
    }
}

#[test]
fn malformed_or_unrelated_collection_attributes_fail_closed() {
    for source in [
        "@collection_algorithm(\"bogus\")\nvar x = AdaptiveTextSet.new()\n",
        "@collection_algorithm(\"hash\")\nvar x = 1\n",
        "@collection_algorithm(\"hash\")\nvar x: AdaptiveTextSet\n",
        "@collection_algorithm(\"hash\")\nfn main(): pass\n",
        "@collection_algorithm(\"hash\")\nvar x = AdaptiveTextSet.clear()\n",
        "@collection_algorithm(\"hash\")\nvar x: AdaptiveTextSet = AdaptiveTextMap.new()\n",
        "@collection_algorithm(\"ordered\")\nvar x = AdaptiveMap.with_attribute()\n",
        "@collection_algorithm(\"auto\")\nvar x = AdaptiveTextSet.with_site_and_target(policy, \"bad-site\", \"target\")\n",
        "@collection_algorithm(\"auto\")\nvar x = AdaptiveTextSet.with_site_and_target(policy, site, target)\n",
    ] {
        assert!(Parser::new(source).parse().is_err(), "unexpected parse success: {source}");
    }
}
