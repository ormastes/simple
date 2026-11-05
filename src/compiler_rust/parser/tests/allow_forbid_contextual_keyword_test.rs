use simple_parser::Parser;

#[test]
fn allow_and_forbid_work_as_value_bindings_and_reads() {
    let source = r#"
fn main():
    val allow = 1
    val forbid = 2
    print(allow + forbid)
"#;
    Parser::new(source)
        .parse()
        .expect("allow and forbid must work as binding names and expression identifiers");
}

#[test]
fn allow_and_forbid_work_as_import_path_segments() {
    Parser::new("use example.{allow, forbid}\n")
        .parse()
        .expect("allow and forbid must work as import path segments");
}

#[test]
fn aop_allow_and_forbid_keyword_forms_still_parse() {
    for source in [
        "allow pc{ use(utils.**) }\n",
        "forbid pc{ import(domain.**, infrastructure.**) }\n",
    ] {
        let module = Parser::new(source).parse().expect("AOP keyword form must remain valid");
        assert!(
            module
                .items
                .iter()
                .any(|item| matches!(item, simple_parser::ast::Node::ArchitectureRule(_)))
        );
    }
}
