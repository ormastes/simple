// Bug resource_decl_and_sffi_attribute_not_parsed_2026-08-07: the seed parser
// must accept `@sffi(...) resource Name` (Grammar A) like the pure-Simple
// frontend (src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl).
use simple_parser::ast::Node;
use simple_parser::Parser;

fn parse(source: &str) -> Result<simple_parser::ast::Module, String> {
    Parser::new(source).parse().map_err(|e| format!("{e:?}"))
}

#[test]
fn sffi_resource_decl_registers_inert_type() {
    let module = parse(
        "@sffi(prefix: \"rt_io_file\", invalid: -1)\nresource File\n\n@sffi(prefix: \"rt_cuda_primary_ctx\", retain: rt_cuda_primary_ctx_retain, release: rt_cuda_primary_ctx_release, sharing: foreign)\nresource Ctx\n",
    )
    .expect("resource decls parse");
    assert_eq!(module.items.len(), 2);
    let Node::Struct(file) = &module.items[0] else { panic!("expected resource type node") };
    assert_eq!(file.name, "File");
    assert!(file.fields.is_empty() && file.methods.is_empty());
    let sffi = file.attributes.iter().find(|a| a.name == "sffi").expect("@sffi kept");
    let named = sffi.named_args.as_ref().expect("named args");
    assert_eq!(named[0].0, "prefix");
    assert!(format!("{:?}", named[0].1).contains("rt_io_file"));
    assert_eq!(named[1].0, "invalid");
    let Node::Struct(ctx) = &module.items[1] else { panic!("expected resource type node") };
    let keys: Vec<&str> = ctx.attributes[0].named_args.as_ref().unwrap().iter().map(|(k, _)| k.as_str()).collect();
    assert_eq!(keys, ["prefix", "retain", "release", "sharing"]);
}

#[test]
fn resource_requires_sffi_with_prefix_and_known_keys() {
    assert!(parse("resource File\n").unwrap_err().contains("@sffi"));
    assert!(parse("@sffi(invalid: 0)\nresource File\n").unwrap_err().contains("prefix"));
    assert!(parse("@sffi(prefix: \"rt_x\", bogus: 1)\nresource File\n").unwrap_err().contains("bogus"));
}

#[test]
fn resource_stays_a_soft_keyword() {
    let module = parse("fn f():\n    var resource = 1\n    resource = resource + 1\n").expect("identifier use parses");
    assert_eq!(module.items.len(), 1);
}
